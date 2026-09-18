/-
The uniform Kolmogorov moment bound of the rescaled reward field on the box
(`parking.tex:3192-3203`).

The cutoff reward of the directed scaling limit, read on the lattice of
rescaled grid points, is the grid field

  `V_n(m,j) = -n^{-1/4} Φ_{N-m}(layerPoint m j)`,   `N = ⌊nT⌋`.

Its piecewise bilinear interpolation `hatInterp` read at
`(ns, √n y + ns/2)` is the continuous reward `G_n` on the box
`[0,T] × [-2A,2A]` whose convergence in law in `C(K)` is the hypothesis `hlaw`
of `Parking.tendsto_integral_orientedCutoffValue`.

This module proves the Kolmogorov input for `G_n`: at one fixed `p > 8`,

  `E|G_n(u) - G_n(u')|^p ≤ M (dist u u')^{p/4}`,   `u,u'` in the box,

uniformly in `n`, from the crossed scenery moment bound of
`Parking.exists_oriented_potential_scenery_bound`.  The estimate is in two
regimes: pairs at distance at least `1/n` are compared through the corners of
their cells and the two-point grid moment bound; pairs within a cell are read
off the Lipschitz constants of the interpolation weights and the partition of
unity.
-/
import Parking.Support.TightInterp
import Parking.Support.TightReward
import Parking.Generic.PolyGrowth

open MeasureTheory LatticeProb Parking.Generic.PolyGrowth

noncomputable section
namespace Parking

/-- The grid reward field at scale `n` with horizon `N`: minus the rescaled
potential of the remaining horizon `N - m` at the layer point `(m, j)`.  The
truncated subtraction makes the field zero beyond the horizon. -/
def orientedGridReward (n N : ℕ) (η : Site 2 → ℝ) (m j : ℤ) : ℝ :=
  -(n : ℝ) ^ (-(1 : ℝ) / 4) *
    orientedPotential η (N - m.toNat) (orientedLayerPoint m.toNat j)

/-- **The grid reward is measurable in the scenery.** -/
theorem measurable_orientedGridReward (n N : ℕ) (m j : ℤ) :
    Measurable fun η : Site 2 → ℝ => orientedGridReward n N η m j :=
  measurable_const.mul
    (measurable_orientedPotential (N - m.toNat) (orientedLayerPoint m.toNat j))

/-- **The grid reward vanishes beyond the horizon.** -/
theorem orientedGridReward_eq_zero_of_le {n N : ℕ} {m : ℤ} (h : N ≤ m.toNat)
    (j : ℤ) (η : Site 2 → ℝ) : orientedGridReward n N η m j = 0 := by
  unfold orientedGridReward
  rw [Nat.sub_eq_zero_of_le h, orientedPotential_zero, mul_zero]

/-- **The `p`-th power of the absolute grid increment** is the prefactor
`n^{-p/4}` times the `p`-th power of the absolute potential increment. -/
theorem orientedGridReward_abs_sub_rpow (n N : ℕ) (m m' : ℤ) (j j' : ℤ) (p : ℝ)
    (η : Site 2 → ℝ) :
    |orientedGridReward n N η m j - orientedGridReward n N η m' j'| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η (N - m.toNat) (orientedLayerPoint m.toNat j) -
          orientedPotential η (N - m'.toNat) (orientedLayerPoint m'.toNat j')| ^ p := by
  have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
  have hdiff : orientedGridReward n N η m j - orientedGridReward n N η m' j' =
      (n : ℝ) ^ (-(1 : ℝ) / 4) *
        (orientedPotential η (N - m'.toNat) (orientedLayerPoint m'.toNat j') -
          orientedPotential η (N - m.toNat) (orientedLayerPoint m.toNat j)) := by
    simp only [orientedGridReward]
    ring
  rw [hdiff, abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _),
    abs_sub_comm (orientedPotential η (N - m'.toNat) (orientedLayerPoint m'.toNat j'))
      (orientedPotential η (N - m.toNat) (orientedLayerPoint m.toNat j))]

/-- **The prefactor pulls out of the `2/p`-rooted `p`-th moment as
`n^{-1/2}`.** -/
theorem iidLaw_integral_rpow_neg_quarter (n : ℕ) (p : ℝ) (hp : 0 < p)
    (μ : Measure ℝ) (F : (Site 2 → ℝ) → ℝ) :
    (∫ η : Site 2 → ℝ, |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) * F η| ^ p ∂(iidLaw 2 μ)) ^ (2 / p) =
      (n : ℝ) ^ (-(1 : ℝ) / 2) * (∫ η : Site 2 → ℝ, |F η| ^ p ∂(iidLaw 2 μ)) ^ (2 / p) := by
  have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
  have hpt : ∀ η : Site 2 → ℝ, |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) * F η| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p * |F η| ^ p := by
    intro η
    rw [abs_mul, abs_neg, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
  simp only [hpt]
  rw [integral_const_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _)
    (integral_nonneg (fun η => Real.rpow_nonneg (abs_nonneg _) p))]
  congr 1
  rw [← Real.rpow_mul (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  have h2 : p * (2 / p) = 2 := by
    rw [mul_comm p (2 / p), div_mul_cancel₀ 2 (ne_of_gt hp)]
  rw [h2]
  norm_num

/-- **The layer-point difference identity**: for `m ≤ m'` the later layer point
is the earlier one displaced by the layer point of the differences. -/
theorem orientedLayerPoint_add {m m' : ℕ} (h : m ≤ m') (j j' : ℤ) :
    orientedLayerPoint m' j' =
      orientedLayerPoint m j + orientedLayerPoint (m' - m) (j' - j) := by
  funext i
  fin_cases i <;>
    simp [orientedLayerPoint, Pi.add_apply] <;>
    push_cast [Nat.cast_sub h] <;>
    ring

/-- **The increment moment of the grid reward field**: the `2/p`-rooted `p`-th
moment of the increment between `(m, j)` and `(m', j')` is bounded by the
crossed scenery estimate over the effective layer difference. -/
theorem exists_orientedGridReward_moment_bound (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ), 0 ≤ m → m ≤ m' →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.sqrt (((min m'.toNat N - min m.toNat N : ℕ) : ℝ)) +
            |(j' - j : ℝ) - (((min m'.toNat N - min m.toNat N : ℕ) : ℝ)) / 2| + 1 / 2)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound (realLaw ν) p hp
    (integrable_rpow_realLaw ν hν p hp0) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n N m m' j j' hm0 hmm => ?_⟩
  set a : ℕ := m.toNat with ha
  set a' : ℕ := m'.toNat with ha'
  have haa' : a ≤ a' := by omega
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- package: from a potential-level estimate `hpot` for `F`, conclude the grid estimate
  have finish : ∀ (F : (Site 2 → ℝ) → ℝ) (B : ℝ),
      (∀ η : Site 2 → ℝ, |orientedGridReward n N η m j - orientedGridReward n N η m' j'| ^ p =
          |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) * F η| ^ p) →
      Integrable (fun η => |F η| ^ p) (iidLaw 2 (realLaw ν)) →
      (∫ η, |F η| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤ C * B →
      B ≤ Real.sqrt (((min a' N - min a N : ℕ) : ℝ)) +
            |(j' - j : ℝ) - (((min a' N - min a N : ℕ) : ℝ)) / 2| + 1 / 2 →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * ((n : ℝ) ^ (-(1 : ℝ) / 2) *
          (Real.sqrt (((min a' N - min a N : ℕ) : ℝ)) +
            |(j' - j : ℝ) - (((min a' N - min a N : ℕ) : ℝ)) / 2| + 1 / 2)) := by
    intro F B hpt hFi hFB hBle
    have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
    have hpt' : ∀ η : Site 2 → ℝ, |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) * F η| ^ p =
        ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p * |F η| ^ p := by
      intro η
      rw [abs_mul, abs_neg, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
    refine ⟨?_, ?_⟩
    · exact ((hFi.const_mul _).congr (Filter.Eventually.of_forall fun η => (hpt' η).symm)).congr
        (Filter.Eventually.of_forall fun η => (hpt η).symm)
    · rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
        iidLaw_integral_rpow_neg_quarter n p hpp (realLaw ν) F]
      calc (n : ℝ) ^ (-(1 : ℝ) / 2) * (∫ η, |F η| ^ p ∂(iidLaw 2 (realLaw ν))) ^ (2 / p)
          ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) * (C * B) :=
            mul_le_mul_of_nonneg_left hFB hnn
        _ = C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * B) := by ring
        _ ≤ C * ((n : ℝ) ^ (-(1 : ℝ) / 2) *
            (Real.sqrt (((min a' N - min a N : ℕ) : ℝ)) +
              |(j' - j : ℝ) - (((min a' N - min a N : ℕ) : ℝ)) / 2| + 1 / 2)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hBle hnn) hC.le
  rcases lt_or_ge N a' with ha'N | ha'N
  · rcases lt_or_ge N a with haN | haN
    · -- both points beyond the horizon: the increment vanishes
      have hz : ∀ η : Site 2 → ℝ, |orientedGridReward n N η m j -
            orientedGridReward n N η m' j'| ^ p = 0 := by
        intro η
        have h1 : orientedGridReward n N η m j = 0 :=
          orientedGridReward_eq_zero_of_le (by omega) j η
        have h2 : orientedGridReward n N η m' j' = 0 :=
          orientedGridReward_eq_zero_of_le (by omega) j' η
        rw [h1, h2, sub_zero, abs_zero]
        exact Real.zero_rpow (ne_of_gt hpp)
      refine ⟨?_, ?_⟩
      · exact (integrable_zero _ _ _).congr (Filter.Eventually.of_forall fun η => (hz η).symm)
      · have hInt : (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
            orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) = 0 := by
          rw [integral_congr_ae (Filter.Eventually.of_forall hz)]
          simp
        rw [hInt, Real.zero_rpow (by positivity : (2 : ℝ) / p ≠ 0)]
        exact mul_nonneg hC.le (mul_nonneg hnn (by positivity))
    · -- only the later point beyond the horizon: single-moment bound
      set D₀ : ℤ := round (((N - a : ℕ) : ℝ) / 2) with hD₀
      have hkey := hb 0 (N - a) D₀ (orientedLayerPoint a j)
      have hcongr : (fun η : Site 2 → ℝ =>
            |orientedPotential η (0 + (N - a)) (orientedLayerPoint a j) -
              orientedPotential η 0 (orientedLayerPoint a j +
                orientedLayerPoint (N - a) D₀)| ^ p)
          = (fun η : Site 2 → ℝ =>
            |orientedPotential η (N - a) (orientedLayerPoint a j)| ^ p) := by
        funext η
        rw [zero_add, orientedPotential_zero, sub_zero]
      rw [hcongr] at hkey
      have hpt : ∀ η : Site 2 → ℝ, |orientedGridReward n N η m j -
            orientedGridReward n N η m' j'| ^ p =
          |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) *
            (orientedPotential η (N - a) (orientedLayerPoint a j))| ^ p := by
        intro η
        have h0 : orientedGridReward n N η m' j' = 0 :=
          orientedGridReward_eq_zero_of_le (by omega) j' η
        rw [h0, sub_zero]
        simp only [orientedGridReward]
        rw [← ha]
      have hDbound : |(D₀ : ℝ) - ((N - a : ℕ) : ℝ) / 2| ≤ 1 / 2 := by
        rw [hD₀, abs_sub_comm]
        exact abs_sub_round _
      refine finish _ (Real.sqrt (((N - a : ℕ) : ℝ)) + 1 / 2) hpt hkey.1 (le_trans hkey.2
        (mul_le_mul_of_nonneg_left (by
          linarith [hDbound]) hC.le)) ?_
      have hmin : min a' N = N := min_eq_right (by omega)
      have hmin' : min a N = a := min_eq_left (by omega)
      rw [hmin, hmin']
      have habs : (0 : ℝ) ≤ |(j' - j : ℝ) - (((N - a : ℕ) : ℝ)) / 2| := abs_nonneg _
      linarith [Real.sqrt_nonneg (((N - a : ℕ) : ℝ))]
  · -- both points below the horizon: the two-point scenery bound
    have hmin : min a' N = a' := min_eq_left (by omega)
    have hmin' : min a N = a := min_eq_left (by omega)
    have hkey := hb (N - a') (a' - a) (j' - j) (orientedLayerPoint a j)
    have hhor : N - a' + (a' - a) = N - a := by omega
    have hsite : orientedLayerPoint a j + orientedLayerPoint (a' - a) (j' - j) =
        orientedLayerPoint a' j' := (orientedLayerPoint_add haa' j j').symm
    rw [hhor, hsite] at hkey
    have hpt : ∀ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p =
        |(-(n : ℝ) ^ (-(1 : ℝ) / 4)) *
          (orientedPotential η (N - a) (orientedLayerPoint a j) -
            orientedPotential η (N - a') (orientedLayerPoint a' j'))| ^ p := by
      intro η
      simp only [orientedGridReward]
      rw [← ha, ← ha']
      congr 1
      congr 1
      ring
    refine finish _ _ hpt hkey.1 hkey.2 ?_
    rw [hmin, hmin']
    push_cast
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1 / 2)


/-- The box `[0,T] × [-2A,2A]` as a set in `Fin 2 → ℝ`. -/
def orientedBox (T A : ℝ) : Set (Fin 2 → ℝ) :=
  Set.Icc ![0, -(2 * A)] ![T, 2 * A]

/-- The rescaled reward process at scale `n`: the interpolation of the grid
reward field of horizon `⌊nT⌋`, read at the mapped point
`(n·s, √n·y + n·s/2)`. -/
def orientedBoxReward (T : ℝ) (n : ℕ) (η : Site 2 → ℝ) (u : Fin 2 → ℝ) : ℝ :=
  hatInterp (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η)
    ((n : ℝ) * u 0, Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2)

/-- **The box reward is measurable in the scenery.** -/
theorem measurable_orientedBoxReward (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ) :
    Measurable fun η : Site 2 → ℝ => orientedBoxReward T n η u := by
  have h : (fun η : Site 2 → ℝ => orientedBoxReward T n η u) = fun η =>
      ∑ m ∈ ({⌊(n : ℝ) * u 0⌋, ⌊(n : ℝ) * u 0⌋ + 1} : Finset ℤ),
        ∑ j ∈ ({⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋,
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ + 1} : Finset ℤ),
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j *
            (hat1 ((n : ℝ) * u 0 - (m : ℝ)) *
              hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (j : ℝ))) := by
    funext η
    rw [orientedBoxReward, hatInterp_eq_corners]
  rw [h]
  apply Finset.measurable_sum
  intro m _
  apply Finset.measurable_sum
  intro j _
  exact Measurable.mul (measurable_orientedGridReward n ⌊(n : ℝ) * T⌋₊ m j) measurable_const

/-- **The box reward has continuous paths.** -/
theorem continuous_orientedBoxReward (T : ℝ) (n : ℕ) (η : Site 2 → ℝ) :
    Continuous fun u : Fin 2 → ℝ => orientedBoxReward T n η u := by
  unfold orientedBoxReward
  apply (continuous_hatInterp _).comp
  exact Continuous.prodMk (continuous_const.mul (continuous_apply 0))
    ((continuous_const.mul (continuous_apply 1)).add
      ((continuous_const.mul (continuous_apply 0)).div_const 2))

/-- **Cell-corner decomposition**: the value at `u` minus the value at the
lower-left corner of its cell is the weight sum of the corner increments. -/
theorem orientedBoxReward_sub_corner (T : ℝ) (n : ℕ) (η : Site 2 → ℝ)
    (u : Fin 2 → ℝ) (m₀ j₀ : ℤ)
    (hm₀ : m₀ = ⌊(n : ℝ) * u 0⌋)
    (hj₀ : j₀ = ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋) :
    orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m₀ j₀ =
      ∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
        (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m j -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η m₀ j₀) *
          (hat1 ((n : ℝ) * u 0 - (m : ℝ)) *
            hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (j : ℝ))) := by
  set V : ℤ → ℤ → ℝ := orientedGridReward n ⌊(n : ℝ) * T⌋₊ η with hV
  set ũ : ℝ × ℝ := ((n : ℝ) * u 0, Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2) with hũ
  have hm₀' : ⌊ũ.1⌋ = m₀ := hm₀.symm
  have hj₀' : ⌊ũ.2⌋ = j₀ := hj₀.symm
  have hG : hatInterp V ũ =
      ∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
        V m j * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) := by
    rw [hatInterp_eq_corners, hm₀', hj₀']
  have hw : ∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
      hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ)) = 1 := by
    rw [← hm₀', ← hj₀']
    exact hatInterp_weight_sum ũ _ _
      (fun m hm => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hat1_ne_zero_mem_floor_pair hm)
      (fun j hj => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hat1_ne_zero_mem_floor_pair hj)
  have hexp : ∀ m j : ℤ, (V m j - V m₀ j₀) * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) =
      V m j * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) -
        V m₀ j₀ * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) :=
    fun m j => sub_mul _ _ _
  calc hatInterp V ũ - V m₀ j₀
      = (∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
            V m j * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ)))) -
          V m₀ j₀ * (∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
            hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) := by rw [hG, hw, mul_one]
    _ = (∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
            V m j * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ)))) -
          (∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
            V m₀ j₀ * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ)))) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
    _ = ∑ m ∈ ({m₀, m₀ + 1} : Finset ℤ), ∑ j ∈ ({j₀, j₀ + 1} : Finset ℤ),
            (V m j - V m₀ j₀) * (hat1 (ũ.1 - (m : ℝ)) * hat1 (ũ.2 - (j : ℝ))) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun m _ => by
            rw [← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => (hexp m j).symm


/-- **The `p`-th power of a sum is bounded by the cardinality power times the
sum of the `p`-th powers.** -/
theorem abs_sum_rpow_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    |∑ c ∈ S, a c| ^ p ≤ (S.card : ℝ) ^ p * ∑ c ∈ S, |a c| ^ p := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    rw [Finset.sum_empty, Finset.sum_empty, abs_zero,
      Real.zero_rpow (ne_of_gt (lt_of_lt_of_le one_pos hp))]
    positivity
  · obtain ⟨c₀, hc₀, hmax⟩ := S.exists_max_image (fun c => |a c|) hS
    have h1 : |∑ c ∈ S, a c| ≤ (S.card : ℝ) * |a c₀| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [show (∑ c ∈ S, |a c|) = ∑ c ∈ S, |a c| from rfl]
      have := Finset.sum_le_card_nsmul S (fun c => |a c|) (|a c₀|) (fun c hc => hmax c hc)
      rwa [nsmul_eq_mul] at this
    have h2 : |a c₀| ^ p ≤ ∑ c ∈ S, |a c| ^ p :=
      Finset.single_le_sum (fun c _ => Real.rpow_nonneg (abs_nonneg _) _) hc₀
    calc |∑ c ∈ S, a c| ^ p ≤ ((S.card : ℝ) * |a c₀|) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) h1 hp0
      _ = (S.card : ℝ) ^ p * |a c₀| ^ p :=
          Real.mul_rpow (Nat.cast_nonneg _) (abs_nonneg _)
      _ ≤ (S.card : ℝ) ^ p * ∑ c ∈ S, |a c| ^ p :=
          mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **From a `2/p`-rooted bound to the `p`-th moment bound.** -/
theorem le_rpow_half_of_rpow_two_div_le {x Y p : ℝ} (hx : 0 ≤ x) (_hY : 0 ≤ Y) (hp : 0 < p)
    (h : x ^ (2 / p) ≤ Y) : x ≤ Y ^ (p / 2) := by
  have h1 : x = (x ^ (2 / p)) ^ (p / 2) := by
    rw [← Real.rpow_mul hx]
    have h2 : (2 : ℝ) / p * (p / 2) = 1 := by field_simp
    rw [h2, Real.rpow_one]
  conv_lhs => rw [h1]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx _) h (by positivity)

/-- **The `(n^{-1/2})^{p/2} = n^{-p/4}` power algebra of the moment bound.** -/
theorem rpow_neg_half_rpow_half (n : ℕ) (p : ℝ) :
    ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ (p / 2) = (n : ℝ) ^ (-(p / 4)) := by
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

/-- **The grid increment `p`-th moment, unordered-pair form**: any pair of
nonnegative layers, with the bracket read on the ordered pair. -/
theorem exists_orientedGridReward_moment_rpow_le (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ) (B : ℝ),
      0 ≤ m → 0 ≤ m' → 0 ≤ B →
      Real.sqrt (((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ)) +
          |(if m ≤ m' then ((j' : ℝ) - j) else ((j : ℝ) - j')) -
            (((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ)) / 2| + 1 / 2 ≤ B →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * B) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_moment_bound ν hν p hp
  refine ⟨C, hC, fun n N m m' j j' B hm0 hm'0 hB0 hBle => ?_⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hraise : ∀ X : ℝ, 0 ≤ X → X ^ (2 / p) ≤ C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * B) →
      X ≤ (C * B) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
    intro X hX0 hXB
    have h1 := le_rpow_half_of_rpow_two_div_le hX0
      (mul_nonneg hC.le (mul_nonneg hnn hB0)) hpp hXB
    rw [show (C * ((n : ℝ) ^ (-(1 : ℝ) / 2) * B)) ^ (p / 2) =
        ((C * B) * (n : ℝ) ^ (-(1 : ℝ) / 2)) ^ (p / 2) by ring_nf] at h1
    rw [Real.mul_rpow (mul_nonneg hC.le hB0) hnn, rpow_neg_half_rpow_half] at h1
    exact h1
  rcases lt_or_ge m' m with hlt | hle
  · -- m' < m: swap the pair
    rw [max_eq_left hlt.le, min_eq_right hlt.le, if_neg (not_le.mpr hlt)] at hBle
    have hb' := hb n N m' m j' j hm'0 hlt.le
    have hcongr : (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
            orientedGridReward n N η m' j'| ^ p)
        = (fun η : Site 2 → ℝ => |orientedGridReward n N η m' j' -
            orientedGridReward n N η m j| ^ p) := by
      funext η
      rw [abs_sub_comm]
    refine ⟨hcongr ▸ hb'.1, ?_⟩
    rw [hcongr]
    exact hraise _ (integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _)
      (le_trans hb'.2 (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBle hnn) hC.le))
  · -- m ≤ m'
    rw [max_eq_right hle, min_eq_left hle, if_pos hle] at hBle
    have hb' := hb n N m m' j j' hm0 hle
    refine ⟨hb'.1, ?_⟩
    exact hraise _ (integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _)
      (le_trans hb'.2 (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBle hnn) hC.le))

/-- **Floors of nearby points differ by at most one.** -/
theorem abs_intFloor_sub_le {x y : ℝ} (h : |x - y| ≤ 1) : |⌊x⌋ - ⌊y⌋| ≤ 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have h5 := abs_le.mp h
  have hlo : (-2 : ℝ) < (⌊x⌋ : ℝ) - ⌊y⌋ := by linarith
  have hhi : (⌊x⌋ : ℝ) - ⌊y⌋ < 2 := by linarith
  have hlo' : (-2 : ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast hlo
  have hhi' : ⌊x⌋ - ⌊y⌋ < 2 := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> omega

/-- **The clamped layer difference is bounded by the true layer
difference.** -/
theorem orientedGrid_clampedDiff_le (N : ℕ) {m m' : ℤ} (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) ≤ |(m : ℝ) - m'| := by
  have e1r : (m.toNat : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm
  have e2r : (m'.toNat : ℝ) = (m' : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm'
  rcases lt_or_ge m m' with h | h
  · have hle0 : m ≤ m' := h.le
    have htt : m.toNat ≤ m'.toNat := by
      have e1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
      have e2 : (m'.toNat : ℤ) = m' := Int.toNat_of_nonneg (le_trans hm hle0)
      omega
    have hle : min m'.toNat N - min m.toNat N ≤ m'.toNat - m.toNat := by
      rcases lt_or_ge m'.toNat N with h1 | h1 <;> rcases lt_or_ge m.toNat N with h2 | h2
      · rw [min_eq_left h1.le, min_eq_left h2.le]
      · rw [min_eq_left h1.le, min_eq_right h2]; omega
      · rw [min_eq_right h1, min_eq_left h2.le]; omega
      · rw [min_eq_right h1, min_eq_right h2]; omega
    have hcast : ((m'.toNat - m.toNat : ℕ) : ℝ) = |(m : ℝ) - m'| := by
      rw [Nat.cast_sub htt, e1r, e2r,
        abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hle0 : (m : ℝ) ≤ m'))]
      ring
    rw [max_eq_right hle0, min_eq_left hle0]
    exact le_trans (by exact_mod_cast hle) hcast.le
  · have htt : m'.toNat ≤ m.toNat := by
      have e1 : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
      have e2 : (m'.toNat : ℤ) = m' := Int.toNat_of_nonneg hm'
      omega
    have hle : min m.toNat N - min m'.toNat N ≤ m.toNat - m'.toNat := by
      rcases lt_or_ge m.toNat N with h1 | h1 <;> rcases lt_or_ge m'.toNat N with h2 | h2
      · rw [min_eq_left h1.le, min_eq_left h2.le]
      · rw [min_eq_left h1.le, min_eq_right h2]; omega
      · rw [min_eq_right h1, min_eq_left h2.le]; omega
      · rw [min_eq_right h1, min_eq_right h2]; omega
    have hcast : ((m.toNat - m'.toNat : ℕ) : ℝ) = |(m : ℝ) - m'| := by
      rw [Nat.cast_sub htt, e1r, e2r,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h : (m' : ℝ) ≤ m))]
    rw [max_eq_left h, min_eq_right h]
    exact le_trans (by exact_mod_cast hle) hcast.le

/-- **The increment moment with the bracket read off the coordinate
differences**: the clamped quantities are replaced by the true differences. -/
theorem exists_orientedGridReward_moment_of_close (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ),
      0 ≤ m → 0 ≤ m' →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * (Real.sqrt |(m : ℝ) - m'| + (|(j : ℝ) - j'| + |(m : ℝ) - m'| / 2) + 1 / 2)) ^
          (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_moment_rpow_le ν hν p hp
  refine ⟨C, hC, fun n N m m' j j' hm hm' => ?_⟩
  have hΔ0 : (0 : ℝ) ≤
      ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) / 2 :=
    by positivity
  have hΔle : ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) ≤ |(m : ℝ) - m'| :=
    orientedGrid_clampedDiff_le N hm hm'
  have hsqrt : Real.sqrt ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) ≤
      Real.sqrt |(m : ℝ) - m'| := Real.sqrt_le_sqrt hΔle
  have hd : |(if m ≤ m' then ((j' : ℝ) - j) else ((j : ℝ) - j'))| = |(j : ℝ) - j'| := by
    by_cases h : m ≤ m'
    · rw [if_pos h, abs_sub_comm]
    · rw [if_neg h]
  have htri : |(if m ≤ m' then ((j' : ℝ) - j) else ((j : ℝ) - j')) -
        ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) / 2| ≤
      |(j : ℝ) - j'| + ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) / 2 := by
    have e : (if m ≤ m' then ((j' : ℝ) - j) else ((j : ℝ) - j')) -
          ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) / 2 =
        (if m ≤ m' then ((j' : ℝ) - j) else ((j : ℝ) - j')) +
          -(((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) / 2) :=
      sub_eq_add_neg _ _
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    rw [hd, abs_neg, abs_of_nonneg hΔ0]
  have hB0 : (0 : ℝ) ≤
      Real.sqrt |(m : ℝ) - m'| + (|(j : ℝ) - j'| + |(m : ℝ) - m'| / 2) + 1 / 2 := by
    positivity
  exact hb n N m m' j j' _ hm hm' hB0 (by linarith [hsqrt, htri, hΔle])

/-- **The corner increment moment**: grid points at coordinate distance at
most two have bracket at most five. -/
theorem exists_orientedGridReward_corner_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ),
      0 ≤ m → 0 ≤ m' → |(m : ℝ) - m'| ≤ 2 → |(j : ℝ) - j'| ≤ 2 →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_moment_of_close ν hν p hp
  refine ⟨C, hC, fun n N m m' j j' hm hm' hm2 hj2 => ?_⟩
  obtain ⟨hint, hbound⟩ := hb n N m m' j j' hm hm'
  refine ⟨hint, le_trans hbound ?_⟩
  have hs : Real.sqrt |(m : ℝ) - m'| ≤ 3 / 2 := by
    calc Real.sqrt |(m : ℝ) - m'| ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hm2
      _ ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 / 2 := by
          rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
  have hB : Real.sqrt |(m : ℝ) - m'| + (|(j : ℝ) - j'| + |(m : ℝ) - m'| / 2) + 1 / 2 ≤ 5 := by
    linarith
  have h0 : (0 : ℝ) ≤
      C * (Real.sqrt |(m : ℝ) - m'| + (|(j : ℝ) - j'| + |(m : ℝ) - m'| / 2) + 1 / 2) := by
    positivity
  have hle : C * (Real.sqrt |(m : ℝ) - m'| + (|(j : ℝ) - j'| + |(m : ℝ) - m'| / 2) + 1 / 2) ≤
      C * 5 := mul_le_mul_of_nonneg_left hB hC.le
  have hrpow := Real.rpow_le_rpow h0 hle (by linarith : (0 : ℝ) ≤ p / 2)
  exact mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The floor difference is bounded by the real difference plus one.** -/
theorem abs_floor_sub_le (x y : ℝ) : |(⌊x⌋ : ℝ) - ⌊y⌋| ≤ |x - y| + 1 := by
  have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have h4 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have h5 := neg_abs_le (x - y)
  have h6 := le_abs_self (x - y)
  rw [abs_le]
  constructor <;> linarith

/-- **The `p`-th power of a three-term sum.** -/
theorem abs_add_add_rpow_le (a b c p : ℝ) (hp : 1 ≤ p) :
    |a + b + c| ^ p ≤ 3 ^ p * (|a| ^ p + |b| ^ p + |c| ^ p) := by
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  set M := max (max |a| |b|) |c| with hM
  have hM0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (le_max_right _ _)
  have ha : |a| ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : |b| ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc : |c| ≤ M := le_max_right _ _
  have h1 : |a + b + c| ≤ 3 * M := by
    calc |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 3 * M := by linarith
  have h2 : M ^ p ≤ |a| ^ p + |b| ^ p + |c| ^ p := by
    rcases le_total (max |a| |b|) |c| with hmc | hmc
    · rw [hM, max_eq_right hmc]
      exact le_add_of_nonneg_left
        (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _))
    · rw [hM, max_eq_left hmc]
      rcases le_total |a| |b| with hab | hab
      · rw [max_eq_right hab]
        exact le_trans (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
      · rw [max_eq_left hab]
        exact le_trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
          (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
  calc |a + b + c| ^ p ≤ (3 * M) ^ p := Real.rpow_le_rpow (abs_nonneg _) h1 hp0
    _ = 3 ^ p * M ^ p := Real.mul_rpow (by norm_num) hM0
    _ ≤ 3 ^ p * (|a| ^ p + |b| ^ p + |c| ^ p) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) _)

/-- **The grid reward depends on the layer only through its natural
clamp.** -/
theorem orientedGridReward_toNat (n N : ℕ) (η : Site 2 → ℝ) (m j : ℤ) :
    orientedGridReward n N η m j = orientedGridReward n N η (m.toNat : ℤ) j := by
  simp only [orientedGridReward, Int.toNat_natCast]

/-- **The single-point moment of the grid reward**: bounded by the square
root of the remaining horizon. -/
theorem exists_orientedGridReward_single_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m j : ℤ),
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j| ^ p)
        (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * (Real.sqrt (((N - m.toNat : ℕ) : ℝ)) + 1 / 2)) ^ (p / 2) *
          (n : ℝ) ^ (-(p / 4)) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hpp : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨C, hC, hb⟩ := exists_oriented_potential_scenery_bound (realLaw ν) p hp
    (integrable_rpow_realLaw ν hν p hp0) (realLaw_mean ν hν)
  refine ⟨C, hC, fun n N m j => ?_⟩
  set h : ℕ := N - m.toNat with hh
  set D : ℤ := round ((h : ℝ) / 2) with hD
  have hkey0 := hb 0 h D (orientedLayerPoint m.toNat j)
  have hcongr : (fun η : Site 2 → ℝ =>
        |orientedPotential η (0 + h) (orientedLayerPoint m.toNat j) -
          orientedPotential η 0 (orientedLayerPoint m.toNat j + orientedLayerPoint h D)| ^ p)
      = (fun η : Site 2 → ℝ =>
        |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p) := by
    funext η
    rw [zero_add, orientedPotential_zero, sub_zero]
  have hkey : Integrable (fun η : Site 2 → ℝ =>
        |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤
        C * (Real.sqrt h + |(D : ℝ) - (h : ℝ) / 2|) :=
    ⟨hcongr ▸ hkey0.1, hcongr ▸ hkey0.2⟩
  have hpt : ∀ η : Site 2 → ℝ, |orientedGridReward n N η m j| ^ p =
      ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
        |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p := by
    intro η
    have hc : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 4) := by positivity
    simp only [orientedGridReward]
    rw [← hh, abs_mul, abs_neg, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg _)]
  have hc : (0 : ℝ) ≤ ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p := by positivity
  have hDbound : |(D : ℝ) - (h : ℝ) / 2| ≤ 1 / 2 := by
    rw [hD, abs_sub_comm]
    exact abs_sub_round ((h : ℝ) / 2)
  have hroot : (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p
        ∂(iidLaw 2 (realLaw ν))) ^ (2 / p) ≤ C * (Real.sqrt (h : ℝ) + 1 / 2) :=
    le_trans hkey.2 (mul_le_mul_of_nonneg_left (by linarith [hDbound]) hC.le)
  have hint : (∫ η : Site 2 → ℝ, |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p
        ∂(iidLaw 2 (realLaw ν))) ≤ (C * (Real.sqrt (h : ℝ) + 1 / 2)) ^ (p / 2) :=
    le_rpow_half_of_rpow_two_div_le (integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _)
      (mul_nonneg hC.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num))) hpp hroot
  constructor
  · exact (hkey.1.const_mul _).congr
      (Filter.Eventually.of_forall fun η => (hpt η).symm)
  · have hpre : (n : ℝ) ^ (-(p / 4)) = ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p := by
      rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      congr 1
      ring
    calc ∫ η : Site 2 → ℝ, |orientedGridReward n N η m j| ^ p ∂(iidLaw 2 (realLaw ν))
        = ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p *
          ∫ η : Site 2 → ℝ, |orientedPotential η h (orientedLayerPoint m.toNat j)| ^ p
            ∂(iidLaw 2 (realLaw ν)) := by
          simp only [hpt]
          rw [integral_const_mul]
      _ ≤ ((n : ℝ) ^ (-(1 : ℝ) / 4)) ^ p * (C * (Real.sqrt (h : ℝ) + 1 / 2)) ^ (p / 2) :=
          mul_le_mul_of_nonneg_left hint hc
      _ = (C * (Real.sqrt (((N - m.toNat : ℕ) : ℝ)) + 1 / 2)) ^ (p / 2) *
            (n : ℝ) ^ (-(p / 4)) := by rw [hpre, hh]; ring

/-- **The corner increment moment, unrestricted layers**: the layer
coordinates enter only through their natural clamps, so the nonnegativity
hypothesis is free. -/
theorem exists_orientedGridReward_corner_moment' (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ),
      |(m : ℝ) - m'| ≤ 2 → |(j : ℝ) - j'| ≤ 2 →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_corner_moment ν hν p hp
  refine ⟨C, hC, fun n N m m' j j' hm hj => ?_⟩
  have hcongr : (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
        orientedGridReward n N η m' j'| ^ p) =
      (fun η : Site 2 → ℝ => |orientedGridReward n N η (m.toNat : ℤ) j -
        orientedGridReward n N η (m'.toNat : ℤ) j'| ^ p) := by
    funext η
    rw [orientedGridReward_toNat n N η m j, orientedGridReward_toNat n N η m' j']
  have hm' : |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| ≤ 2 := by
    have e1 : (((m.toNat : ℤ)) : ℝ) = max (m : ℝ) 0 := by
      rw [Int.toNat_eq_max]
      push_cast
      rfl
    have e2 : (((m'.toNat : ℤ)) : ℝ) = max (m' : ℝ) 0 := by
      rw [Int.toNat_eq_max]
      push_cast
      rfl
    rw [e1, e2]
    exact le_trans (abs_max_sub_max_le_abs (m : ℝ) (m' : ℝ) 0) hm
  exact hcongr ▸ hb n N (m.toNat : ℤ) (m'.toNat : ℤ) j j' (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hm' hj

/-- **The cell-corner moment**: the value at `u` is close in `p`-th moment to
the lower-left corner of its cell, with bound `4^{p+1} (5C)^{p/2} n^{-p/4}`. -/
theorem exists_orientedBoxReward_cell_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (n : ℕ) (u : Fin 2 → ℝ), (0 : ℝ) ≤ u 0 →
      Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        4 ^ (p + 1) * ((C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_corner_moment' ν hν p hp
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) hp
  refine ⟨C, hC, fun T n u hu0 => ?_⟩
  set m₀ : ℤ := ⌊(n : ℝ) * u 0⌋ with hm₀
  set j₀ : ℤ := ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ with hj₀
  set N : ℕ := ⌊(n : ℝ) * T⌋₊ with hN
  set S₁ : Finset ℤ := {m₀, m₀ + 1} with hS₁
  set S₂ : Finset ℤ := {j₀, j₀ + 1} with hS₂
  set P : Finset (ℤ × ℤ) := S₁ ×ˢ S₂ with hP
  have hcard : P.card = 4 := by
    rw [hP, Finset.card_product, hS₁, hS₂, Finset.card_pair (by omega),
      Finset.card_pair (by omega)]
  have hcorner : ∀ c : ℤ × ℤ, c ∈ P →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
    rw [hS₁] at hc1
    rw [hS₂] at hc2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    have hm2 : |(c.1 : ℝ) - (m₀ : ℝ)| ≤ 2 := by
      rcases hc1 with h | h
      · rw [h, sub_self, abs_zero]; norm_num
      · rw [h]
        have e : ((m₀ + 1 : ℤ) : ℝ) - (m₀ : ℝ) = 1 := by push_cast; ring
        rw [e, abs_one]; norm_num
    have hj2 : |(c.2 : ℝ) - (j₀ : ℝ)| ≤ 2 := by
      rcases hc2 with h | h
      · rw [h, sub_self, abs_zero]; norm_num
      · rw [h]
        have e : ((j₀ + 1 : ℤ) : ℝ) - (j₀ : ℝ) = 1 := by push_cast; ring
        rw [e, abs_one]; norm_num
    exact hb n N c.1 m₀ c.2 j₀ hm2 hj2
  have hpoint : ∀ η : Site 2 → ℝ,
      |orientedBoxReward T n η u - orientedGridReward n N η m₀ j₀| ^ p ≤
      4 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
        orientedGridReward n N η m₀ j₀| ^ p := by
    intro η
    have hdec := orientedBoxReward_sub_corner T n η u m₀ j₀ hm₀ hj₀
    rw [← hN] at hdec
    rw [hdec, ← Finset.sum_product']
    refine le_trans (abs_sum_rpow_le P _ p hp1) ?_
    rw [hcard]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    apply Finset.sum_le_sum
    intro c hc
    have hw0 : (0 : ℝ) ≤ hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
        hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ)) :=
      mul_nonneg (hat1_nonneg _) (hat1_nonneg _)
    have hw1 : hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
        hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ)) ≤ 1 :=
      le_trans (mul_le_mul (hat1_le_one _) (hat1_le_one _) (hat1_nonneg _) zero_le_one)
        (one_mul 1).le
    rw [abs_mul, abs_of_nonneg hw0, Real.mul_rpow (abs_nonneg _) hw0]
    calc |orientedGridReward n N η c.1 c.2 - orientedGridReward n N η m₀ j₀| ^ p *
            (hat1 ((n : ℝ) * u 0 - (c.1 : ℝ)) *
              hat1 (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2 - (c.2 : ℝ))) ^ p
        ≤ |orientedGridReward n N η c.1 c.2 - orientedGridReward n N η m₀ j₀| ^ p * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hw0 hw1 hp0)
            (Real.rpow_nonneg (abs_nonneg _) _)
      _ = |orientedGridReward n N η c.1 c.2 - orientedGridReward n N η m₀ j₀| ^ p := mul_one _
  have hgInt : Integrable (fun η : Site 2 → ℝ =>
        4 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p) (iidLaw 2 (realLaw ν)) :=
    (integrable_finsetSum P fun c hc => (hcorner c hc).1).const_mul _
  have hfMeas : Measurable fun η : Site 2 → ℝ =>
      |orientedBoxReward T n η u - orientedGridReward n N η m₀ j₀| ^ p :=
    measurable_abs_rpow ((measurable_orientedBoxReward T n u).sub
      (measurable_orientedGridReward n N m₀ j₀)) p
  constructor
  · exact hgInt.mono' hfMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint η)
  · have hfInt : Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
          orientedGridReward n N η m₀ j₀| ^ p) (iidLaw 2 (realLaw ν)) :=
      hgInt.mono' hfMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun η => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact hpoint η)
    calc ∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν))
        ≤ ∫ η : Site 2 → ℝ, 4 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
            orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν)) :=
          integral_mono_ae hfInt hgInt (Filter.Eventually.of_forall hpoint)
      _ = 4 ^ p * ∑ c ∈ P, ∫ η : Site 2 → ℝ, |orientedGridReward n N η c.1 c.2 -
            orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν)) := by
          rw [integral_const_mul]
          rw [integral_finsetSum P fun c hc => (hcorner c hc).1]
      _ ≤ 4 ^ p * ∑ c ∈ P, (C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun c hc => (hcorner c hc).2)
            (Real.rpow_nonneg (by norm_num) _)
      _ = 4 ^ (p + 1) * ((C * 5) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          have h4 : (4 : ℝ) ^ (p + 1) = 4 ^ p * 4 := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 4) p 1, Real.rpow_one]
          rw [h4]
          ring

/-- **The clamped layer difference equals the true layer difference** when
both layers are below the horizon. -/
theorem orientedGrid_clampedDiff_eq {N : ℕ} {m m' : ℤ} (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (hN : (max m m').toNat ≤ N) :
    ((min (max m m').toNat N - min (min m m').toNat N : ℕ) : ℝ) = |(m : ℝ) - m'| := by
  have htt : (min m m').toNat ≤ (max m m').toNat := by
    have e1 : ((min m m').toNat : ℤ) = min m m' := Int.toNat_of_nonneg (le_min hm hm')
    have e2 : ((max m m').toNat : ℤ) = max m m' :=
      Int.toNat_of_nonneg (le_trans hm (le_max_left _ _))
    omega
  have hmax : min (max m m').toNat N = (max m m').toNat := min_eq_left hN
  have hmin : min (min m m').toNat N = (min m m').toNat := min_eq_left (le_trans htt hN)
  have e1r : (((max m m').toNat : ℕ) : ℝ) = max (m : ℝ) m' := by
    have h1 : (((max m m').toNat : ℕ) : ℤ) = max m m' :=
      Int.toNat_of_nonneg (le_trans hm (le_max_left _ _))
    calc (((max m m').toNat : ℕ) : ℝ) = (((max m m').toNat : ℤ) : ℝ) := by norm_cast
      _ = ((max m m' : ℤ) : ℝ) := by rw [h1]
      _ = max (m : ℝ) m' := by push_cast; ring
  have e2r : (((min m m').toNat : ℕ) : ℝ) = min (m : ℝ) m' := by
    have h1 : (((min m m').toNat : ℕ) : ℤ) = min m m' := Int.toNat_of_nonneg (le_min hm hm')
    calc (((min m m').toNat : ℕ) : ℝ) = (((min m m').toNat : ℤ) : ℝ) := by norm_cast
      _ = ((min m m' : ℤ) : ℝ) := by rw [h1]
      _ = min (m : ℝ) m' := by push_cast; ring
  rw [hmax, hmin, Nat.cast_sub htt, e1r, e2r]
  rcases le_total (m : ℝ) m' with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]

/-- **The centered difference of two floor pairs** is the centered real
difference up to the rounding error `3/2`. -/
theorem abs_floor_sub_half_floor_sub_le (a b c d : ℝ) :
    |(⌊a⌋ : ℝ) - ⌊b⌋ - (((⌊c⌋ : ℝ) - ⌊d⌋) / 2)| ≤ |a - b - (c - d) / 2| + 3 / 2 := by
  have ha0 : (0 : ℝ) ≤ a - ⌊a⌋ := sub_nonneg.mpr (Int.floor_le a)
  have ha1 : a - ⌊a⌋ < 1 := by linarith [Int.lt_floor_add_one a]
  have hb0 : (0 : ℝ) ≤ b - ⌊b⌋ := sub_nonneg.mpr (Int.floor_le b)
  have hb1 : b - ⌊b⌋ < 1 := by linarith [Int.lt_floor_add_one b]
  have hc0 : (0 : ℝ) ≤ c - ⌊c⌋ := sub_nonneg.mpr (Int.floor_le c)
  have hc1 : c - ⌊c⌋ < 1 := by linarith [Int.lt_floor_add_one c]
  have hd0 : (0 : ℝ) ≤ d - ⌊d⌋ := sub_nonneg.mpr (Int.floor_le d)
  have hd1 : d - ⌊d⌋ < 1 := by linarith [Int.lt_floor_add_one d]
  have h5 := neg_abs_le (a - b - (c - d) / 2)
  have h6 := le_abs_self (a - b - (c - d) / 2)
  rw [abs_le]
  constructor <;> linarith

/-- **The power cancellation** `n^{p/4} · n^{-p/4} = 1`. -/
theorem rpow_quarter_mul_rpow_neg_quarter (n : ℕ) (hn : 1 ≤ n) (p : ℝ) :
    (n : ℝ) ^ (p / 4) * (n : ℝ) ^ (-(p / 4)) = 1 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_add hn0]
  simp

/-- **The square-root-to-power scaling** `(√(nρ))^{p/2} · n^{-p/4} = ρ^{p/4}`. -/
theorem sqrt_rpow_half_mul_rpow_neg_quarter (n : ℕ) (hn : 1 ≤ n) {ρ p : ℝ} (hρ : 0 ≤ ρ) :
    (Real.sqrt ((n : ℝ) * ρ)) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) = ρ ^ (p / 4) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg hn0.le hρ),
    show (1 : ℝ) / 2 * (p / 2) = p / 4 by ring, Real.mul_rpow hn0.le hρ, mul_assoc,
    mul_comm (ρ ^ (p / 4)) ((n : ℝ) ^ (-(p / 4))), ← mul_assoc,
    rpow_quarter_mul_rpow_neg_quarter n hn p, one_mul]

/-- **Cast of the natural clamp.** -/
theorem toNat_cast_real {m : ℤ} (hm : 0 ≤ m) : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg hm

set_option maxHeartbeats 1000000 in
/-- **The far corner-to-corner moment**: for pairs at rescaled distance at
least `1/n`, the increment of the grid reward between the two cell corners
has `p`-th moment bounded by `M (dist u u')^{p/4}`, with `M` itself bounded by
`K * (1 + A) ^ (p / 2)` for a SINGLE constant `K`, chosen before `A` and independent of it. -/
theorem exists_orientedBoxReward_far_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ), 0 ≤ A → ∃ M : ℝ, 0 ≤ M ∧ M ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) (u u' : Fin 2 → ℝ),
      u ∈ orientedBox T A → u' ∈ orientedBox T A →
      (1 : ℝ) ≤ (n : ℝ) * dist u u' →
      Integrable (fun η : Site 2 → ℝ =>
          |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ,
          |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p
            ∂(iidLaw 2 (realLaw ν))) ≤
        M * (dist u u') ^ (p / 4) := by
  obtain ⟨C₁, hC₁, hb⟩ := exists_orientedGridReward_moment_rpow_le ν hν p hp
  obtain ⟨C₂, hC₂, hsingle⟩ := exists_orientedGridReward_single_moment ν hν p hp
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp4 : (0 : ℝ) ≤ p / 4 := by positivity
  have hp2 : (0 : ℝ) ≤ p / 2 := by positivity
  set K₁ : ℝ := Real.sqrt 2 + 3 with hK₁
  set K₃ : ℝ := Real.sqrt 2 + 1 / 2 with hK₃
  have hK₁0 : (0 : ℝ) ≤ K₁ := by rw [hK₁]; positivity
  have hK₃0 : (0 : ℝ) ≤ K₃ := by rw [hK₃]; positivity
  have hCK₁ : (0 : ℝ) ≤ C₁ * K₁ := mul_nonneg hC₁.le hK₁0
  have hCK₃ : (0 : ℝ) ≤ C₂ * K₃ := mul_nonneg hC₂.le hK₃0
  have hCK₁' : (0 : ℝ) ≤ C₁ * (Real.sqrt (T + 1) + 6) := mul_nonneg hC₁.le (by positivity)
  refine ⟨(C₁ * K₁) ^ (p / 2) + (C₁ * (Real.sqrt (T + 1) + 6)) ^ (p / 2) + (C₂ * K₃) ^ (p / 2),
    add_nonneg (add_nonneg (Real.rpow_nonneg hCK₁ _) (Real.rpow_nonneg hCK₁' _))
      (Real.rpow_nonneg hCK₃ _),
    fun A hA => ?_⟩
  set K₂ : ℝ := Real.sqrt (T + 1) + 4 * A + 2 with hK₂
  have hK₂0 : (0 : ℝ) ≤ K₂ := by rw [hK₂]; positivity
  have hCK₂ : (0 : ℝ) ≤ C₁ * K₂ := mul_nonneg hC₁.le hK₂0
  refine ⟨(C₁ * K₁) ^ (p / 2) + (C₁ * K₂) ^ (p / 2) + (C₂ * K₃) ^ (p / 2),
    add_nonneg (add_nonneg (Real.rpow_nonneg hCK₁ _) (Real.rpow_nonneg hCK₂ _))
      (Real.rpow_nonneg hCK₃ _),
    ?_,
    fun n hn u u' hu hu' hnρ => ?_⟩
  · -- The explicit polynomial-in-`A` bound on the witness `M`.
    have hK2_le : K₂ ≤ (Real.sqrt (T + 1) + 6) * (1 + A) := by
      rw [hK₂]
      nlinarith [Real.sqrt_nonneg (T + 1), mul_nonneg (Real.sqrt_nonneg (T + 1)) hA]
    have hCK2_le : C₁ * K₂ ≤ (C₁ * (Real.sqrt (T + 1) + 6)) * (1 + A) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hK2_le hC₁.le
    have hterm2 : (C₁ * K₂) ^ (p / 2) ≤
        (C₁ * (Real.sqrt (T + 1) + 6)) ^ (p / 2) * (1 + A) ^ (p / 2) := by
      calc (C₁ * K₂) ^ (p / 2)
          ≤ ((C₁ * (Real.sqrt (T + 1) + 6)) * (1 + A)) ^ (p / 2) :=
            Real.rpow_le_rpow hCK₂ hCK2_le hp2
        _ = (C₁ * (Real.sqrt (T + 1) + 6)) ^ (p / 2) * (1 + A) ^ (p / 2) :=
            Real.mul_rpow (mul_nonneg hC₁.le (by positivity)) (by linarith)
    have hterm1 : (C₁ * K₁) ^ (p / 2) ≤ (C₁ * K₁) ^ (p / 2) * (1 + A) ^ (p / 2) :=
      le_mul_of_one_le_right (Real.rpow_nonneg hCK₁ _) (one_le_one_add_rpow hA hp2)
    have hterm3 : (C₂ * K₃) ^ (p / 2) ≤ (C₂ * K₃) ^ (p / 2) * (1 + A) ^ (p / 2) :=
      le_mul_of_one_le_right (Real.rpow_nonneg hCK₃ _) (one_le_one_add_rpow hA hp2)
    calc (C₁ * K₁) ^ (p / 2) + (C₁ * K₂) ^ (p / 2) + (C₂ * K₃) ^ (p / 2)
        ≤ (C₁ * K₁) ^ (p / 2) * (1 + A) ^ (p / 2) +
            (C₁ * (Real.sqrt (T + 1) + 6)) ^ (p / 2) * (1 + A) ^ (p / 2) +
            (C₂ * K₃) ^ (p / 2) * (1 + A) ^ (p / 2) :=
          add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = ((C₁ * K₁) ^ (p / 2) + (C₁ * (Real.sqrt (T + 1) + 6)) ^ (p / 2) +
            (C₂ * K₃) ^ (p / 2)) * (1 + A) ^ (p / 2) := by ring
  have hn0ℝ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  set N : ℕ := ⌊(n : ℝ) * T⌋₊ with hN
  set ρ : ℝ := dist u u' with hρdef
  have hρ0 : (0 : ℝ) ≤ ρ := dist_nonneg
  obtain ⟨hu00, hu0T, hu1lo, hu1hi⟩ : (0 : ℝ) ≤ u 0 ∧ u 0 ≤ T ∧ -(2 * A) ≤ u 1 ∧
      u 1 ≤ 2 * A := by
    rw [orientedBox, Set.mem_Icc] at hu
    have h0 := hu.1 0
    have h1 := hu.2 0
    have h2 := hu.1 1
    have h3 := hu.2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  obtain ⟨hu'00, hu'0T, hu'1lo, hu'1hi⟩ : (0 : ℝ) ≤ u' 0 ∧ u' 0 ≤ T ∧ -(2 * A) ≤ u' 1 ∧
      u' 1 ≤ 2 * A := by
    rw [orientedBox, Set.mem_Icc] at hu'
    have h0 := hu'.1 0
    have h1 := hu'.2 0
    have h2 := hu'.1 1
    have h3 := hu'.2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  have hd0 : |u 0 - u' 0| ≤ ρ := by
    have h := dist_le_pi_dist u u' 0
    rw [Real.dist_eq] at h
    exact h
  have hd1 : |u 1 - u' 1| ≤ ρ := by
    have h := dist_le_pi_dist u u' 1
    rw [Real.dist_eq] at h
    exact h
  have hdm : |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| ≤ (n : ℝ) * ρ + 1 := by
    calc |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋|
        ≤ |(n : ℝ) * u 0 - (n : ℝ) * u' 0| + 1 := abs_floor_sub_le _ _
      _ = (n : ℝ) * |u 0 - u' 0| + 1 := by rw [← mul_sub, abs_mul, abs_of_nonneg hn0ℝ]
      _ ≤ (n : ℝ) * ρ + 1 := by linarith [mul_le_mul_of_nonneg_left hd0 hn0ℝ]
  have hcenter : |(⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
        ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
        (((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2)| ≤
      Real.sqrt n * ρ + 3 / 2 := by
    have h := abs_floor_sub_half_floor_sub_le
      (Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2) (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2)
      ((n : ℝ) * u' 0) ((n : ℝ) * u 0)
    have e1 : (Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2) -
          (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2) -
        ((n : ℝ) * u' 0 - (n : ℝ) * u 0) / 2 = Real.sqrt n * (u' 1 - u 1) := by ring
    rw [e1] at h
    have e2 : |Real.sqrt n * (u' 1 - u 1)| = Real.sqrt n * |u 1 - u' 1| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm]
    rw [e2] at h
    exact le_trans h
      (add_le_add_left (mul_le_mul_of_nonneg_left hd1 (Real.sqrt_nonneg (n : ℝ))) _)
  rcases lt_or_ge N ⌊(n : ℝ) * u' 0⌋.toNat with h₁ | h₁ <;>
    rcases lt_or_ge N ⌊(n : ℝ) * u 0⌋.toNat with h₀ | h₀
  · -- both corners beyond the horizon: the increment vanishes
    have hzero : (fun η : Site 2 → ℝ =>
        |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
          orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) = fun _ => 0 := by
      funext η
      rw [orientedGridReward_eq_zero_of_le h₀.le _ η,
        orientedGridReward_eq_zero_of_le h₁.le _ η, sub_self, abs_zero,
        Real.zero_rpow (by linarith : p ≠ 0)]
    refine ⟨?_, ?_⟩
    · rw [hzero]
      exact integrable_const 0
    · rw [hzero]
      simp only [integral_const, smul_zero]
      exact mul_nonneg
        (add_nonneg (add_nonneg (Real.rpow_nonneg hCK₁ _) (Real.rpow_nonneg hCK₂ _))
          (Real.rpow_nonneg hCK₃ _))
        (Real.rpow_nonneg hρ0 _)
  · -- only the second corner is beyond the horizon: single moment at the first
    have hcongr : (fun η : Site 2 → ℝ =>
        |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
          orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) =
        fun η : Site 2 → ℝ => |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p := by
      funext η
      rw [orientedGridReward_eq_zero_of_le h₁.le _ η, sub_zero]
    obtain ⟨hint0, hbound0⟩ := hsingle n N ⌊(n : ℝ) * u 0⌋
      ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋
    have hm₀0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu00)
    have hm₁0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u' 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu'00)
    have hle : ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ) ≤
        |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| := by
      have h1 : N - ⌊(n : ℝ) * u 0⌋.toNat ≤ ⌊(n : ℝ) * u' 0⌋.toNat - ⌊(n : ℝ) * u 0⌋.toNat := by
        omega
      have h2 : ⌊(n : ℝ) * u 0⌋.toNat ≤ ⌊(n : ℝ) * u' 0⌋.toNat := by omega
      calc ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ)
          ≤ ((⌊(n : ℝ) * u' 0⌋.toNat - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ) :=
            Nat.cast_le.mpr h1
        _ = (⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋ := by
            rw [Nat.cast_sub h2, toNat_cast_real hm₁0, toNat_cast_real hm₀0]
        _ = |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| := by
            rw [abs_of_nonpos]
            · ring
            · have e : (⌊(n : ℝ) * u 0⌋ : ℝ) ≤ ⌊(n : ℝ) * u' 0⌋ := by
                have e1 : (⌊(n : ℝ) * u 0⌋.toNat : ℤ) = ⌊(n : ℝ) * u 0⌋ :=
                  Int.toNat_of_nonneg hm₀0
                have e2 : (⌊(n : ℝ) * u' 0⌋.toNat : ℤ) = ⌊(n : ℝ) * u' 0⌋ :=
                  Int.toNat_of_nonneg hm₁0
                have : ⌊(n : ℝ) * u 0⌋ ≤ ⌊(n : ℝ) * u' 0⌋ := by omega
                exact_mod_cast this
              exact sub_nonpos.mpr e
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ρ) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_le_sqrt hnρ
    have hX : Real.sqrt ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ) + 1 / 2 ≤
        K₃ * Real.sqrt ((n : ℝ) * ρ) := by
      have hs : Real.sqrt ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ) ≤
          Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := by
        calc Real.sqrt ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ)
            ≤ Real.sqrt (2 * ((n : ℝ) * ρ)) :=
              Real.sqrt_le_sqrt (le_trans hle (by linarith [hdm, hnρ]))
          _ = Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_mul (by norm_num) _
      have e : K₃ * Real.sqrt ((n : ℝ) * ρ) =
          Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) + (1 / 2) * Real.sqrt ((n : ℝ) * ρ) := by
        rw [hK₃]; ring
      linarith
    refine ⟨hcongr ▸ hint0, ?_⟩
    have hcrw : (fun η : Site 2 → ℝ =>
        |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
          orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) =
        fun η : Site 2 → ℝ => |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p := hcongr
    rw [hcrw]
    calc ∫ η : Site 2 → ℝ, |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))
        ≤ (C₂ * (Real.sqrt ((N - ⌊(n : ℝ) * u 0⌋.toNat : ℕ) : ℝ) + 1 / 2)) ^ (p / 2) *
            (n : ℝ) ^ (-(p / 4)) := hbound0
      _ ≤ (C₂ * (K₃ * Real.sqrt ((n : ℝ) * ρ))) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0ℝ _)
          exact Real.rpow_le_rpow
            (mul_nonneg hC₂.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num)))
            (mul_le_mul_of_nonneg_left hX hC₂.le) hp2
      _ = (C₂ * K₃) ^ (p / 2) * ρ ^ (p / 4) := by
          have e : C₂ * (K₃ * Real.sqrt ((n : ℝ) * ρ)) = (C₂ * K₃) * Real.sqrt ((n : ℝ) * ρ) := by
            ring
          rw [e, Real.mul_rpow hCK₃ (Real.sqrt_nonneg _), mul_assoc,
            sqrt_rpow_half_mul_rpow_neg_quarter n hn hρ0]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ0 _)
          exact le_trans (le_add_of_nonneg_left
            (add_nonneg (Real.rpow_nonneg hCK₁ _) (Real.rpow_nonneg hCK₂ _)))
            (le_refl _)
  · -- only the first corner is beyond the horizon: single moment at the second
    have hcongr : (fun η : Site 2 → ℝ =>
        |orientedGridReward n N η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
          orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) =
        fun η : Site 2 → ℝ => |orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
          ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p := by
      funext η
      rw [orientedGridReward_eq_zero_of_le h₀.le _ η, zero_sub, abs_neg]
    obtain ⟨hint0, hbound0⟩ := hsingle n N ⌊(n : ℝ) * u' 0⌋
      ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋
    have hm₀0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu00)
    have hm₁0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u' 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu'00)
    have hle : ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ) ≤
        |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| := by
      have h1 : N - ⌊(n : ℝ) * u' 0⌋.toNat ≤ ⌊(n : ℝ) * u 0⌋.toNat - ⌊(n : ℝ) * u' 0⌋.toNat := by
        omega
      have h2 : ⌊(n : ℝ) * u' 0⌋.toNat ≤ ⌊(n : ℝ) * u 0⌋.toNat := by omega
      calc ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ)
          ≤ ((⌊(n : ℝ) * u 0⌋.toNat - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ) :=
            Nat.cast_le.mpr h1
        _ = (⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋ := by
            rw [Nat.cast_sub h2, toNat_cast_real hm₀0, toNat_cast_real hm₁0]
        _ = |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| := by
            rw [abs_of_nonneg]
            have e : (⌊(n : ℝ) * u' 0⌋ : ℝ) ≤ ⌊(n : ℝ) * u 0⌋ := by
              have e1 : (⌊(n : ℝ) * u 0⌋.toNat : ℤ) = ⌊(n : ℝ) * u 0⌋ :=
                Int.toNat_of_nonneg hm₀0
              have e2 : (⌊(n : ℝ) * u' 0⌋.toNat : ℤ) = ⌊(n : ℝ) * u' 0⌋ :=
                Int.toNat_of_nonneg hm₁0
              have : ⌊(n : ℝ) * u' 0⌋ ≤ ⌊(n : ℝ) * u 0⌋ := by omega
              exact_mod_cast this
            exact sub_nonneg.mpr e
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ρ) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_le_sqrt hnρ
    have hX : Real.sqrt ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ) + 1 / 2 ≤
        K₃ * Real.sqrt ((n : ℝ) * ρ) := by
      have hs : Real.sqrt ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ) ≤
          Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := by
        calc Real.sqrt ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ)
            ≤ Real.sqrt (2 * ((n : ℝ) * ρ)) :=
              Real.sqrt_le_sqrt (le_trans hle (by linarith [hdm, hnρ]))
          _ = Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_mul (by norm_num) _
      have e : K₃ * Real.sqrt ((n : ℝ) * ρ) =
          Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) + (1 / 2) * Real.sqrt ((n : ℝ) * ρ) := by
        rw [hK₃]; ring
      linarith
    refine ⟨hcongr ▸ hint0, ?_⟩
    rw [hcongr]
    calc ∫ η : Site 2 → ℝ, |orientedGridReward n N η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))
        ≤ (C₂ * (Real.sqrt ((N - ⌊(n : ℝ) * u' 0⌋.toNat : ℕ) : ℝ) + 1 / 2)) ^ (p / 2) *
            (n : ℝ) ^ (-(p / 4)) := hbound0
      _ ≤ (C₂ * (K₃ * Real.sqrt ((n : ℝ) * ρ))) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0ℝ _)
          exact Real.rpow_le_rpow
            (mul_nonneg hC₂.le (add_nonneg (Real.sqrt_nonneg _) (by norm_num)))
            (mul_le_mul_of_nonneg_left hX hC₂.le) hp2
      _ = (C₂ * K₃) ^ (p / 2) * ρ ^ (p / 4) := by
          have e : C₂ * (K₃ * Real.sqrt ((n : ℝ) * ρ)) = (C₂ * K₃) * Real.sqrt ((n : ℝ) * ρ) := by
            ring
          rw [e, Real.mul_rpow hCK₃ (Real.sqrt_nonneg _), mul_assoc,
            sqrt_rpow_half_mul_rpow_neg_quarter n hn hρ0]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ0 _)
          exact le_add_of_nonneg_left
            (add_nonneg (Real.rpow_nonneg hCK₁ _) (Real.rpow_nonneg hCK₂ _))
  · -- both corners below the horizon: the centered two-point bound
    have hm₀0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu00)
    have hm₁0 : (0 : ℤ) ≤ ⌊(n : ℝ) * u' 0⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hn0ℝ hu'00)
    have hmaxN : (max ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat ≤ N := by
      rcases max_choice ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋ with h | h <;> rw [h] <;> assumption
    have hΔeq : ((min (max ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N -
          min (min ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N : ℕ) : ℝ) =
        |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| :=
      orientedGrid_clampedDiff_eq hm₀0 hm₁0 hmaxN
    have hDeq : |(if ⌊(n : ℝ) * u 0⌋ ≤ ⌊(n : ℝ) * u' 0⌋ then
          (⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋
        else (⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ : ℝ) -
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋) -
        |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| / 2| =
      |(⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
        (((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2)| := by
      by_cases h : ⌊(n : ℝ) * u 0⌋ ≤ ⌊(n : ℝ) * u' 0⌋
      · rw [if_pos h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h :
            (⌊(n : ℝ) * u 0⌋ : ℝ) ≤ ⌊(n : ℝ) * u' 0⌋))]
        congr 1
        ring
      · rw [if_neg h]
        have hlt : ⌊(n : ℝ) * u' 0⌋ < ⌊(n : ℝ) * u 0⌋ := not_le.mp h
        rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le :
            (⌊(n : ℝ) * u' 0⌋ : ℝ) ≤ ⌊(n : ℝ) * u 0⌋))]
        have e : (⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ : ℝ) -
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
            ((⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋) / 2 =
            -((⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              ((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2) := by ring
        rw [e, abs_neg]
    set B : ℝ := Real.sqrt |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| +
      |(⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
          ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
        (((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2)| + 1 / 2 with hB
    have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
    have hbracket : Real.sqrt ((min (max ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N -
          min (min ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N : ℕ) : ℝ) +
        |(if ⌊(n : ℝ) * u 0⌋ ≤ ⌊(n : ℝ) * u' 0⌋ then
            (⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋
          else (⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ : ℝ) -
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋) -
          ((min (max ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N -
            min (min ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋).toNat N : ℕ) : ℝ) / 2| + 1 / 2 ≤ B := by
      rw [hΔeq, hDeq]
    obtain ⟨hint0, hbound0⟩ := hb n N ⌊(n : ℝ) * u 0⌋ ⌊(n : ℝ) * u' 0⌋
      ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ B
      hm₀0 hm₁0 hB0 hbracket
    refine ⟨hint0, le_trans hbound0 ?_⟩
    rcases lt_or_ge ρ 1 with hρ1 | hρ1
    · -- macroscopically close: `B ≤ K₁ √(nρ)`
      have hs : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) * ρ) := by
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_le_sqrt hnρ
      have hρρ : ρ ≤ Real.sqrt ρ := by
        calc ρ = Real.sqrt (ρ ^ 2) := (Real.sqrt_sq hρ0).symm
          _ ≤ Real.sqrt ρ := Real.sqrt_le_sqrt (by nlinarith [hρ0, hρ1.le])
      have hBle : B ≤ K₁ * Real.sqrt ((n : ℝ) * ρ) := by
        have h1 : Real.sqrt |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| ≤
            Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := by
          calc Real.sqrt |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋|
              ≤ Real.sqrt (2 * ((n : ℝ) * ρ)) :=
                Real.sqrt_le_sqrt (by linarith [hdm, hnρ])
            _ = Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_mul (by norm_num) _
        have h2 : |(⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              (((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2)| ≤
            Real.sqrt ((n : ℝ) * ρ) + 3 / 2 := by
          refine le_trans hcenter (add_le_add_left ?_ (3 / 2 : ℝ))
          calc Real.sqrt n * ρ ≤ Real.sqrt n * Real.sqrt ρ :=
                mul_le_mul_of_nonneg_left hρρ (Real.sqrt_nonneg _)
            _ = Real.sqrt ((n : ℝ) * ρ) := (Real.sqrt_mul hn0ℝ ρ).symm
        have e : K₁ * Real.sqrt ((n : ℝ) * ρ) =
            Real.sqrt 2 * Real.sqrt ((n : ℝ) * ρ) + 3 * Real.sqrt ((n : ℝ) * ρ) := by
          rw [hK₁]; ring
        rw [hB]
        linarith
      calc (C₁ * B) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))
          ≤ (C₁ * (K₁ * Real.sqrt ((n : ℝ) * ρ))) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0ℝ _)
            exact Real.rpow_le_rpow (mul_nonneg hC₁.le hB0)
              (mul_le_mul_of_nonneg_left hBle hC₁.le) hp2
        _ = (C₁ * K₁) ^ (p / 2) * ρ ^ (p / 4) := by
            have e : C₁ * (K₁ * Real.sqrt ((n : ℝ) * ρ)) =
                (C₁ * K₁) * Real.sqrt ((n : ℝ) * ρ) := by ring
            rw [e, Real.mul_rpow hCK₁ (Real.sqrt_nonneg _), mul_assoc,
              sqrt_rpow_half_mul_rpow_neg_quarter n hn hρ0]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ0 _)
            exact le_trans (le_add_of_nonneg_right (Real.rpow_nonneg hCK₂ _))
              (le_add_of_nonneg_right (Real.rpow_nonneg hCK₃ _))
    · -- macroscopically separated: `B ≤ K₂ √n`
      have hρ1' : (1 : ℝ) ≤ ρ := hρ1
      have hsn : (1 : ℝ) ≤ Real.sqrt n := by
        calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
          _ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hm₀le : (⌊(n : ℝ) * u 0⌋ : ℝ) ≤ (n : ℝ) * T :=
        le_trans (Int.floor_le _) (mul_le_mul_of_nonneg_left hu0T hn0ℝ)
      have hm₁le : (⌊(n : ℝ) * u' 0⌋ : ℝ) ≤ (n : ℝ) * T :=
        le_trans (Int.floor_le _) (mul_le_mul_of_nonneg_left hu'0T hn0ℝ)
      have hm₀ge : (0 : ℝ) ≤ (⌊(n : ℝ) * u 0⌋ : ℝ) := by exact_mod_cast hm₀0
      have hm₁ge : (0 : ℝ) ≤ (⌊(n : ℝ) * u' 0⌋ : ℝ) := by exact_mod_cast hm₁0
      have hdmT : |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| ≤ (n : ℝ) * T := by
        rw [abs_le]
        constructor <;> linarith
      have hd1A : |u 1 - u' 1| ≤ 4 * A := by
        rw [abs_le]
        constructor <;> linarith
      have hBle : B ≤ K₂ * Real.sqrt n := by
        have h1 : Real.sqrt |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋| ≤
            Real.sqrt n * Real.sqrt (T + 1) := by
          calc Real.sqrt |(⌊(n : ℝ) * u 0⌋ : ℝ) - ⌊(n : ℝ) * u' 0⌋|
              ≤ Real.sqrt ((n : ℝ) * (T + 1)) :=
                Real.sqrt_le_sqrt (by linarith [hdmT, mul_nonneg hn0ℝ hT])
            _ = Real.sqrt n * Real.sqrt (T + 1) := Real.sqrt_mul hn0ℝ _
        have h2 : |(⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ : ℝ) -
              ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              (((⌊(n : ℝ) * u' 0⌋ : ℝ) - ⌊(n : ℝ) * u 0⌋) / 2)| ≤
            Real.sqrt n * (4 * A) + 3 / 2 := by
          have h := abs_floor_sub_half_floor_sub_le
            (Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2)
            (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2)
            ((n : ℝ) * u' 0) ((n : ℝ) * u 0)
          have e1 : (Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2) -
                (Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2) -
              ((n : ℝ) * u' 0 - (n : ℝ) * u 0) / 2 = Real.sqrt n * (u' 1 - u 1) := by ring
          rw [e1] at h
          have e2 : |Real.sqrt n * (u' 1 - u 1)| = Real.sqrt n * |u 1 - u' 1| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm]
          rw [e2] at h
          exact le_trans h
            (add_le_add_left (mul_le_mul_of_nonneg_left hd1A (Real.sqrt_nonneg _)) _)
        have e : K₂ * Real.sqrt n = Real.sqrt n * Real.sqrt (T + 1) +
            Real.sqrt n * (4 * A) + 2 * Real.sqrt n := by
          rw [hK₂]; ring
        rw [hB]
        linarith
      have hnn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc (C₁ * B) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))
          ≤ (C₁ * (K₂ * Real.sqrt n)) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hn0ℝ _)
            exact Real.rpow_le_rpow (mul_nonneg hC₁.le hB0)
              (mul_le_mul_of_nonneg_left hBle hC₁.le) hp2
        _ = (C₁ * K₂) ^ (p / 2) := by
            have e : C₁ * (K₂ * Real.sqrt n) = (C₁ * K₂) * Real.sqrt n := by ring
            rw [e, Real.mul_rpow hCK₂ (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
              ← Real.rpow_mul hn0ℝ, show (1 : ℝ) / 2 * (p / 2) = p / 4 by ring, mul_assoc,
              rpow_quarter_mul_rpow_neg_quarter n hn p, mul_one]
        _ ≤ (C₁ * K₂) ^ (p / 2) * ρ ^ (p / 4) := by
            have : (1 : ℝ) ≤ ρ ^ (p / 4) := Real.one_le_rpow hρ1' hp4
            calc (C₁ * K₂) ^ (p / 2) = (C₁ * K₂) ^ (p / 2) * 1 := (mul_one _).symm
              _ ≤ _ := mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hCK₂ _)
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hρ0 _)
            exact le_trans (le_add_of_nonneg_left (Real.rpow_nonneg hCK₁ _))
              (le_add_of_nonneg_right (Real.rpow_nonneg hCK₃ _))

/-- **Floors of points within `3/2` differ by at most two.** -/
theorem abs_intFloor_sub_le_two {x y : ℝ} (h : |x - y| ≤ 3 / 2) : |⌊x⌋ - ⌊y⌋| ≤ 2 := by
  have hR : |(⌊x⌋ : ℝ) - ⌊y⌋| ≤ 5 / 2 := le_trans (abs_floor_sub_le x y) (by linarith)
  rw [abs_le] at hR
  have h1 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) ≤ 5 / 2 := by exact_mod_cast hR.2
  have h3 : -(5 / 2 : ℝ) ≤ ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast hR.1
  rw [abs_le]
  constructor
  · by_contra hlt
    have h5 : (⌊x⌋ - ⌊y⌋ : ℤ) ≤ -3 := by omega
    have h6 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) ≤ -3 := by exact_mod_cast h5
    linarith
  · by_contra hlt
    have h5 : (3 : ℤ) ≤ ⌊x⌋ - ⌊y⌋ := by omega
    have h6 : (3 : ℝ) ≤ ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast h5
    linarith

/-- **The corner increment moment, offset three in the site coordinate**:
grid points within layer distance two and site distance three have bracket at
most six. -/
theorem exists_orientedGridReward_corner_moment_three (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n N : ℕ) (m m' : ℤ) (j j' : ℤ),
      |(m : ℝ) - m'| ≤ 2 → |(j : ℝ) - j'| ≤ 3 →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η m j -
          orientedGridReward n N η m' j'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * 6) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_moment_of_close ν hν p hp
  refine ⟨C, hC, fun n N m m' j j' hm hj => ?_⟩
  have hcongr : (fun η : Site 2 → ℝ => |orientedGridReward n N η m j -
        orientedGridReward n N η m' j'| ^ p) =
      (fun η : Site 2 → ℝ => |orientedGridReward n N η (m.toNat : ℤ) j -
        orientedGridReward n N η (m'.toNat : ℤ) j'| ^ p) := by
    funext η
    rw [orientedGridReward_toNat n N η m j, orientedGridReward_toNat n N η m' j']
  have hm' : |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| ≤ 2 := by
    have e1 : (((m.toNat : ℤ)) : ℝ) = max (m : ℝ) 0 := by
      rw [Int.toNat_eq_max]
      push_cast
      rfl
    have e2 : (((m'.toNat : ℤ)) : ℝ) = max (m' : ℝ) 0 := by
      rw [Int.toNat_eq_max]
      push_cast
      rfl
    rw [e1, e2]
    exact le_trans (abs_max_sub_max_le_abs (m : ℝ) (m' : ℝ) 0) hm
  obtain ⟨hint, hbound⟩ := hb n N (m.toNat : ℤ) (m'.toNat : ℤ) j j'
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨hcongr ▸ hint, le_trans (hcongr ▸ hbound) ?_⟩
  have hs : Real.sqrt |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| ≤ 3 / 2 := by
    calc Real.sqrt |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| ≤ Real.sqrt 2 :=
          Real.sqrt_le_sqrt hm'
      _ ≤ Real.sqrt (9 / 4) := Real.sqrt_le_sqrt (by norm_num)
      _ = 3 / 2 := by
          rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num]
          exact Real.sqrt_sq (by norm_num)
  have hB : Real.sqrt |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| +
      (|(j : ℝ) - j'| + |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| / 2) + 1 / 2 ≤ 6 := by
    linarith
  have h0 : (0 : ℝ) ≤ C * (Real.sqrt |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| +
      (|(j : ℝ) - j'| + |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| / 2) + 1 / 2) := by
    positivity
  have hle : C * (Real.sqrt |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| +
      (|(j : ℝ) - j'| + |(((m.toNat : ℤ)) : ℝ) - ((m'.toNat : ℤ) : ℝ)| / 2) + 1 / 2) ≤
      C * 6 := mul_le_mul_of_nonneg_left hB hC.le
  have hrpow := Real.rpow_le_rpow h0 hle (by linarith : (0 : ℝ) ≤ p / 2)
  exact mul_le_mul_of_nonneg_right hrpow (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The near moment**: at rescaled distance below `1/n`, the box reward
increment is the weight-difference sum of corner increments over a fixed
`4 × 6` rectangle; the weights vary Lipschitzly and the corner moments are
uniform. -/
theorem exists_orientedBoxReward_near_moment (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (_hn : 1 ≤ n) (u u' : Fin 2 → ℝ),
      (n : ℝ) * dist u u' < 1 →
      Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M * (dist u u') ^ (p / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_orientedGridReward_corner_moment_three ν hν p hp
  have hp0 : (0 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp4 : (0 : ℝ) ≤ p / 4 := by linarith
  have hC60 : (0 : ℝ) ≤ C * 6 := mul_nonneg hC.le (by norm_num)
  refine ⟨24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg hC60 _)) (Real.rpow_nonneg (by norm_num) _),
    fun n hn u u' hnρ => ?_⟩
  set ρ : ℝ := dist u u' with hρ
  set N : ℕ := ⌊(n : ℝ) * T⌋₊ with hN
  set ũ : ℝ × ℝ := ((n : ℝ) * u 0, Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2) with hũ
  set ũ' : ℝ × ℝ := ((n : ℝ) * u' 0, Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2) with hũ'
  set m₀ : ℤ := ⌊ũ.1⌋ with hm₀
  set j₀ : ℤ := ⌊ũ.2⌋ with hj₀
  set S₁ : Finset ℤ := Finset.Icc (m₀ - 1) (m₀ + 2) with hS₁
  set S₂ : Finset ℤ := Finset.Icc (j₀ - 2) (j₀ + 3) with hS₂
  set P : Finset (ℤ × ℤ) := S₁ ×ˢ S₂ with hP
  have hρ0 : (0 : ℝ) ≤ ρ := dist_nonneg
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0ℝ : (0 : ℝ) ≤ (n : ℝ) := hn0.le
  have hnρ0 : (0 : ℝ) ≤ (n : ℝ) * ρ := mul_nonneg hn0ℝ hρ0
  have hρ1 : ρ ≤ 1 := by
    calc ρ = 1 * ρ := (one_mul _).symm
      _ ≤ (n : ℝ) * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hρ0
      _ ≤ 1 := hnρ.le
  have hd0 : |u 0 - u' 0| ≤ ρ := by
    have h := dist_le_pi_dist u u' 0
    rw [Real.dist_eq] at h
    exact h
  have hd1 : |u 1 - u' 1| ≤ ρ := by
    have h := dist_le_pi_dist u u' 1
    rw [Real.dist_eq] at h
    exact h
  have hcard : P.card = 24 := by
    rw [hP, Finset.card_product, hS₁, hS₂, Int.card_Icc, Int.card_Icc,
      show m₀ + 2 + 1 - (m₀ - 1) = (4 : ℤ) by ring,
      show j₀ + 3 + 1 - (j₀ - 2) = (6 : ℤ) by ring]
    rfl
  have hsqrtnρ : Real.sqrt n * ρ ≤ Real.sqrt ((n : ℝ) * ρ) := by
    calc Real.sqrt n * ρ = Real.sqrt n * Real.sqrt (ρ ^ 2) := by rw [Real.sqrt_sq hρ0]
      _ = Real.sqrt ((n : ℝ) * ρ ^ 2) := (Real.sqrt_mul hn0ℝ _).symm
      _ ≤ Real.sqrt ((n : ℝ) * ρ) :=
          Real.sqrt_le_sqrt (by nlinarith [hρ0, hρ1, mul_nonneg hnρ0 (sub_nonneg.mpr hρ1)])
  have hnρsqrt : (n : ℝ) * ρ ≤ Real.sqrt ((n : ℝ) * ρ) := by
    calc (n : ℝ) * ρ = Real.sqrt (((n : ℝ) * ρ) ^ 2) := (Real.sqrt_sq hnρ0).symm
      _ ≤ Real.sqrt ((n : ℝ) * ρ) :=
          Real.sqrt_le_sqrt (by nlinarith [hnρ0, hnρ.le, mul_nonneg hnρ0 (sub_nonneg.mpr hnρ.le)])
  have hsqrtnρ1 : Real.sqrt ((n : ℝ) * ρ) ≤ 1 := by
    calc Real.sqrt ((n : ℝ) * ρ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hnρ.le
      _ = 1 := Real.sqrt_one
  have ht1 : |ũ.1 - ũ'.1| ≤ 1 := by
    have e : ũ.1 - ũ'.1 = (n : ℝ) * (u 0 - u' 0) := by rw [hũ, hũ']; ring
    rw [e, abs_mul, abs_of_nonneg hn0ℝ]
    calc (n : ℝ) * |u 0 - u' 0| ≤ (n : ℝ) * ρ := mul_le_mul_of_nonneg_left hd0 hn0ℝ
      _ ≤ 1 := hnρ.le
  have hfloor1 : |⌊ũ.1⌋ - ⌊ũ'.1⌋| ≤ 1 := abs_intFloor_sub_le ht1
  have hs2 : |ũ.2 - ũ'.2| ≤ Real.sqrt n * ρ + (n : ℝ) * ρ / 2 := by
    have e : ũ.2 - ũ'.2 = Real.sqrt n * (u 1 - u' 1) + (n : ℝ) * (u 0 - u' 0) / 2 := by
      rw [hũ, hũ']
      ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    have e1 : |Real.sqrt n * (u 1 - u' 1)| = Real.sqrt n * |u 1 - u' 1| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have e2 : |(n : ℝ) * (u 0 - u' 0) / 2| = (n : ℝ) * |u 0 - u' 0| / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hn0ℝ, abs_two]
    rw [e1, e2]
    have h1 : Real.sqrt n * |u 1 - u' 1| ≤ Real.sqrt n * ρ :=
      mul_le_mul_of_nonneg_left hd1 (Real.sqrt_nonneg _)
    have h2 := mul_le_mul_of_nonneg_left hd0 hn0ℝ
    linarith
  have hs1 : |ũ.2 - ũ'.2| ≤ 3 / 2 := by linarith [hs2, hsqrtnρ, hsqrtnρ1, hnρ.le]
  have hfloor2 : |⌊ũ.2⌋ - ⌊ũ'.2⌋| ≤ 2 := abs_intFloor_sub_le_two hs1
  have h₁ : ∀ m : ℤ, hat1 (ũ.1 - (m : ℝ)) ≠ 0 → m ∈ S₁ := by
    intro m hm
    rcases hat1_ne_zero_mem_floor_pair hm with h | h
    · rw [hS₁, Finset.mem_Icc, h, ← hm₀]
      omega
    · rw [hS₁, Finset.mem_Icc, h, ← hm₀]
      omega
  have h₁' : ∀ m : ℤ, hat1 (ũ'.1 - (m : ℝ)) ≠ 0 → m ∈ S₁ := by
    intro m hm
    have hfb : |⌊ũ'.1⌋ - m₀| ≤ 1 := by
      rw [hm₀, abs_sub_comm]
      exact hfloor1
    rw [abs_le] at hfb
    rcases hat1_ne_zero_mem_floor_pair hm with h | h
    · rw [hS₁, Finset.mem_Icc, h]
      omega
    · rw [hS₁, Finset.mem_Icc, h]
      omega
  have h₂ : ∀ j : ℤ, hat1 (ũ.2 - (j : ℝ)) ≠ 0 → j ∈ S₂ := by
    intro j hj
    rcases hat1_ne_zero_mem_floor_pair hj with h | h
    · rw [hS₂, Finset.mem_Icc, h, ← hj₀]
      omega
    · rw [hS₂, Finset.mem_Icc, h, ← hj₀]
      omega
  have h₂' : ∀ j : ℤ, hat1 (ũ'.2 - (j : ℝ)) ≠ 0 → j ∈ S₂ := by
    intro j hj
    have hfb : |⌊ũ'.2⌋ - j₀| ≤ 2 := by
      rw [hj₀, abs_sub_comm]
      exact hfloor2
    rw [abs_le] at hfb
    rcases hat1_ne_zero_mem_floor_pair hj with h | h
    · rw [hS₂, Finset.mem_Icc, h]
      omega
    · rw [hS₂, Finset.mem_Icc, h]
      omega
  have hexp : ∀ η : Site 2 → ℝ, orientedBoxReward T n η u - orientedBoxReward T n η u' =
      ∑ c ∈ P, (orientedGridReward n N η c.1 c.2 - orientedGridReward n N η m₀ j₀) *
        ((hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
          (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))) := by
    intro η
    have hGu : orientedBoxReward T n η u =
        ∑ c ∈ P, orientedGridReward n N η c.1 c.2 *
          (hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) := by
      rw [orientedBoxReward, ← hN, ← hũ, hatInterp_eq_sum _ ũ S₁ S₂ h₁ h₂,
        ← Finset.sum_product', ← hP]
    have hGu' : orientedBoxReward T n η u' =
        ∑ c ∈ P, orientedGridReward n N η c.1 c.2 *
          (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ))) := by
      rw [orientedBoxReward, ← hN, ← hũ', hatInterp_eq_sum _ ũ' S₁ S₂ h₁' h₂',
        ← Finset.sum_product', ← hP]
    have hwu : ∑ c ∈ P, hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ)) = 1 := by
      have h := hatInterp_weight_sum ũ S₁ S₂ h₁ h₂
      rw [← Finset.sum_product', ← hP] at h
      exact h
    have hwu' : ∑ c ∈ P, hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)) = 1 := by
      have h := hatInterp_weight_sum ũ' S₁ S₂ h₁' h₂'
      rw [← Finset.sum_product', ← hP] at h
      exact h
    have hper : ∀ c : ℤ × ℤ, orientedGridReward n N η c.1 c.2 *
            (hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
          orientedGridReward n N η c.1 c.2 *
            (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ))) =
        (orientedGridReward n N η c.1 c.2 - orientedGridReward n N η m₀ j₀) *
            ((hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
              (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))) +
          orientedGridReward n N η m₀ j₀ *
            ((hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
              (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))) := fun c => by ring
    rw [hGu, hGu', ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl fun c _ => hper c, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hwu, hwu', sub_self, mul_zero, add_zero]
  have hw : ∀ c : ℤ × ℤ, |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
        (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ≤
      (5 / 2) * Real.sqrt ((n : ℝ) * ρ) := by
    intro c
    refine le_trans (abs_hatWeight_sub_le c ũ ũ') ?_
    have e1 : |ũ.1 - ũ'.1| = (n : ℝ) * |u 0 - u' 0| := by
      have e : ũ.1 - ũ'.1 = (n : ℝ) * (u 0 - u' 0) := by rw [hũ, hũ']; ring
      rw [e, abs_mul, abs_of_nonneg hn0ℝ]
    rw [e1]
    have h0le := mul_le_mul_of_nonneg_left hd0 hn0ℝ
    linarith [hs2, hsqrtnρ, hnρsqrt]
  have hwp : ∀ c : ℤ × ℤ, |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
        (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p ≤
      (5 / 2) ^ p * ((n : ℝ) * ρ) ^ (p / 2) := by
    intro c
    calc |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
            (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p
        ≤ ((5 / 2) * Real.sqrt ((n : ℝ) * ρ)) ^ p :=
          Real.rpow_le_rpow (abs_nonneg _) (hw c) hp0
      _ = (5 / 2) ^ p * (Real.sqrt ((n : ℝ) * ρ)) ^ p :=
          Real.mul_rpow (by norm_num) (Real.sqrt_nonneg _)
      _ = (5 / 2) ^ p * ((n : ℝ) * ρ) ^ (p / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnρ0,
            show (1 : ℝ) / 2 * p = p / 2 by ring]
  have hcorner : ∀ c : ℤ × ℤ, c ∈ P →
      Integrable (fun η : Site 2 → ℝ => |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        (C * 6) ^ (p / 2) * (n : ℝ) ^ (-(p / 4)) := by
    intro c hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
    rw [hS₁, Finset.mem_Icc] at hc1
    rw [hS₂, Finset.mem_Icc] at hc2
    have hm2 : |(c.1 : ℝ) - (m₀ : ℝ)| ≤ 2 := by
      rw [abs_le]
      have hlo : ((m₀ - 1 : ℤ) : ℝ) ≤ (c.1 : ℝ) := by exact_mod_cast hc1.1
      have hhi : (c.1 : ℝ) ≤ ((m₀ + 2 : ℤ) : ℝ) := by exact_mod_cast hc1.2
      push_cast at hlo hhi
      constructor <;> linarith
    have hj3 : |(c.2 : ℝ) - (j₀ : ℝ)| ≤ 3 := by
      rw [abs_le]
      have hlo : ((j₀ - 2 : ℤ) : ℝ) ≤ (c.2 : ℝ) := by exact_mod_cast hc2.1
      have hhi : (c.2 : ℝ) ≤ ((j₀ + 3 : ℤ) : ℝ) := by exact_mod_cast hc2.2
      push_cast at hlo hhi
      constructor <;> linarith
    exact hb n N c.1 m₀ c.2 j₀ hm2 hj3
  have hpoint : ∀ η : Site 2 → ℝ, |orientedBoxReward T n η u -
        orientedBoxReward T n η u'| ^ p ≤
      24 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p *
        |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
          (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p := by
    intro η
    rw [hexp η]
    refine le_trans (abs_sum_rpow_le P _ p hp1) ?_
    rw [hcard]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    apply Finset.sum_le_sum
    intro c _
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hgInt : Integrable (fun η : Site 2 → ℝ =>
      24 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
          orientedGridReward n N η m₀ j₀| ^ p *
        |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
          (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p)
      (iidLaw 2 (realLaw ν)) :=
    (integrable_finsetSum P fun c hc => ((hcorner c hc).1.mul_const _)).const_mul _
  have hfMeas : Measurable fun η : Site 2 → ℝ =>
      |orientedBoxReward T n η u - orientedBoxReward T n η u'| ^ p :=
    measurable_abs_rpow ((measurable_orientedBoxReward T n u).sub
      (measurable_orientedBoxReward T n u')) p
  have hfInt : Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
        orientedBoxReward T n η u'| ^ p) (iidLaw 2 (realLaw ν)) :=
    hgInt.mono' hfMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact hpoint η)
  refine ⟨hfInt, ?_⟩
  have halg : (n : ℝ) ^ (-(p / 4)) * ((n : ℝ) * ρ) ^ (p / 2) =
      ((n : ℝ) * ρ) ^ (p / 4) * ρ ^ (p / 4) := by
    have h1 : (n : ℝ) ^ (-(p / 4)) * (n : ℝ) ^ (p / 2) = (n : ℝ) ^ (p / 4) := by
      rw [← Real.rpow_add hn0, show -(p / 4) + p / 2 = p / 4 by ring]
    have h2 : ρ ^ (p / 2) = ρ ^ (p / 4) * ρ ^ (p / 4) := by
      rcases eq_or_lt_of_le hρ0 with hρz | hρpos
      · rw [← hρz, Real.zero_rpow (by linarith : p / 2 ≠ 0),
          Real.zero_rpow (by linarith : p / 4 ≠ 0), mul_zero]
      · rw [← Real.rpow_add hρpos, show p / 4 + p / 4 = p / 2 by ring]
    rw [Real.mul_rpow hn0ℝ hρ0, ← mul_assoc, h1, h2, ← mul_assoc,
      ← Real.mul_rpow hn0ℝ hρ0]
  calc ∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
        orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν))
      ≤ ∫ η : Site 2 → ℝ, 24 ^ p * ∑ c ∈ P, |orientedGridReward n N η c.1 c.2 -
            orientedGridReward n N η m₀ j₀| ^ p *
          |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
            (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hfInt hgInt (Filter.Eventually.of_forall hpoint)
    _ = 24 ^ p * ∑ c ∈ P, (∫ η : Site 2 → ℝ, |orientedGridReward n N η c.1 c.2 -
            orientedGridReward n N η m₀ j₀| ^ p ∂(iidLaw 2 (realLaw ν))) *
          |(hat1 (ũ.1 - (c.1 : ℝ)) * hat1 (ũ.2 - (c.2 : ℝ))) -
            (hat1 (ũ'.1 - (c.1 : ℝ)) * hat1 (ũ'.2 - (c.2 : ℝ)))| ^ p := by
        rw [integral_const_mul, integral_finsetSum P
          (fun c hc => (hcorner c hc).1.mul_const _)]
        congr 1
        exact Finset.sum_congr rfl fun c _ => integral_mul_const _ _
    _ ≤ 24 ^ p * ∑ c ∈ P, ((C * 6) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))) *
          ((5 / 2) ^ p * ((n : ℝ) * ρ) ^ (p / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
        exact Finset.sum_le_sum fun c hc =>
          mul_le_mul (hcorner c hc).2 (hwp c) (Real.rpow_nonneg (abs_nonneg _) _)
            (mul_nonneg (Real.rpow_nonneg hC60 _) (Real.rpow_nonneg hn0ℝ _))
    _ = 24 ^ p * (24 * (((C * 6) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))) *
          ((5 / 2) ^ p * ((n : ℝ) * ρ) ^ (p / 2)))) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        norm_num
    _ = (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) *
          ((n : ℝ) * ρ) ^ (p / 4) * ρ ^ (p / 4) := by
        have h24 : (24 : ℝ) ^ (p + 1) = 24 ^ p * 24 := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 24) p 1, Real.rpow_one]
        have hperm : 24 ^ p * (24 * (((C * 6) ^ (p / 2) * (n : ℝ) ^ (-(p / 4))) *
            ((5 / 2) ^ p * ((n : ℝ) * ρ) ^ (p / 2)))) =
          (24 ^ p * 24 * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) *
            ((n : ℝ) ^ (-(p / 4)) * ((n : ℝ) * ρ) ^ (p / 2)) := by ring
        rw [hperm, halg, h24]
        ring
    _ ≤ (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) * ρ ^ (p / 4) := by
        have h1 : ((n : ℝ) * ρ) ^ (p / 4) ≤ 1 := Real.rpow_le_one hnρ0 hnρ.le hp4
        have hM0 : (0 : ℝ) ≤ 24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
            (Real.rpow_nonneg hC60 _)) (Real.rpow_nonneg (by norm_num) _)
        calc (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) *
                ((n : ℝ) * ρ) ^ (p / 4) * ρ ^ (p / 4)
            = (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) *
              (((n : ℝ) * ρ) ^ (p / 4) * ρ ^ (p / 4)) := by ring
          _ ≤ (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) * (1 * ρ ^ (p / 4)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hρ0 _)) hM0
          _ = (24 ^ (p + 1) * ((C * 6) ^ (p / 2)) * (5 / 2) ^ p) * ρ ^ (p / 4) := by
              rw [one_mul]

set_option maxHeartbeats 1000000 in
/-- **The Kolmogorov moment package**: the box reward increments have `p`-th
moment uniformly bounded by `M (dist u u')^{p/4}` for all pairs of the box and
all scales `n ≥ 1`, with `M` itself bounded by `K * (1 + A) ^ (p / 2)` for a SINGLE
constant `K`, chosen before `A` and independent of it. -/
theorem exists_orientedBoxReward_kolmogorov (ν : Measure ℤ) (hν : CriticalLaw ν)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ), 0 ≤ A → ∃ M : ℝ, 0 ≤ M ∧ M ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (n : ℕ) (_hn : 1 ≤ n) (u u' : Fin 2 → ℝ),
      u ∈ orientedBox T A → u' ∈ orientedBox T A →
      Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        M * (dist u u') ^ (p / 4) := by
  obtain ⟨K₁, hK₁nn, hK₁all⟩ := exists_orientedBoxReward_far_moment ν hν p hp T hT
  obtain ⟨C₃, hC₃, hcell⟩ := exists_orientedBoxReward_cell_moment ν hν p hp
  obtain ⟨M₂, hM₂, hnear⟩ := exists_orientedBoxReward_near_moment ν hν p hp T
  have hp1 : (1 : ℝ) ≤ p := le_trans (by norm_num) hp
  have hp4 : (0 : ℝ) ≤ p / 4 := by linarith
  have hp2 : (0 : ℝ) ≤ p / 2 := by linarith
  set Mc : ℝ := 4 ^ (p + 1) * (C₃ * 5) ^ (p / 2) with hMc
  have hMc0 : (0 : ℝ) ≤ Mc :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (mul_nonneg hC₃.le (by norm_num)) _)
  refine ⟨3 ^ p * K₁ + (3 ^ p * (2 * Mc) + M₂),
    add_nonneg (mul_nonneg (by positivity) hK₁nn)
      (add_nonneg (mul_nonneg (by positivity) (mul_nonneg (by norm_num) hMc0)) hM₂),
    fun A hA => ?_⟩
  obtain ⟨M₁, hM₁, hM₁bd, hfar⟩ := hK₁all A hA
  have h30 : (0 : ℝ) ≤ 3 ^ p * (2 * Mc + M₁) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (mul_nonneg (by norm_num) hMc0) hM₁)
  refine ⟨3 ^ p * (2 * Mc + M₁) + M₂, add_nonneg h30 hM₂, ?_, fun n hn u u' hu hu' => ?_⟩
  · -- The explicit polynomial-in-`A` bound on the witness `M`.
    have h2 : 3 ^ p * M₁ ≤ (3 ^ p * K₁) * (1 + A) ^ (p / 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hM₁bd (by positivity)
    have hx : 3 ^ p * (2 * Mc + M₁) + M₂ ≤
        (3 ^ p * K₁) * (1 + A) ^ (p / 2) +
          (3 ^ p * (2 * Mc) + M₂) := by nlinarith [h2]
    have hK₂nn : (0 : ℝ) ≤ 3 ^ p * (2 * Mc) + M₂ :=
      add_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (by norm_num) hMc0)) hM₂
    exact le_add_const_mul_one_add_rpow hK₂nn hA hp2 hx
  rcases lt_or_ge ((n : ℝ) * dist u u') 1 with h | h
  · obtain ⟨hint, hbound⟩ := hnear n hn u u' h
    exact ⟨hint, le_trans hbound
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left h30)
        (Real.rpow_nonneg dist_nonneg _))⟩
  · obtain ⟨hfarInt, hfarBound⟩ := hfar n hn u u' hu hu' h
    have hu0 : (0 : ℝ) ≤ u 0 := by
      rw [orientedBox, Set.mem_Icc] at hu
      have h0 := hu.1 0
      simp only [Matrix.cons_val_zero] at h0
      exact h0
    have hu'0 : (0 : ℝ) ≤ u' 0 := by
      rw [orientedBox, Set.mem_Icc] at hu'
      have h0 := hu'.1 0
      simp only [Matrix.cons_val_zero] at h0
      exact h0
    obtain ⟨hcellInt, hcellBound⟩ := hcell T n u hu0
    obtain ⟨hcellInt', hcellBound'⟩ := hcell T n u' hu'0
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcellBound2 : (∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
            ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        Mc * (n : ℝ) ^ (-(p / 4)) :=
      le_trans hcellBound (le_of_eq (by rw [hMc]; ring))
    have hcellBound2' : (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
          ⌊(n : ℝ) * u' 0⌋ ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
          orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        Mc * (n : ℝ) ^ (-(p / 4)) := by
      have hcongr : (fun η : Site 2 → ℝ => |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
            ⌊(n : ℝ) * u' 0⌋ ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
            orientedBoxReward T n η u'| ^ p) =
          (fun η : Site 2 → ℝ => |orientedBoxReward T n η u' -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) := by
        funext η
        rw [abs_sub_comm]
      rw [hcongr]
      exact le_trans hcellBound' (le_of_eq (by rw [hMc]; ring))
    have hcellInt3 : Integrable (fun η : Site 2 → ℝ =>
        |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
            ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
          orientedBoxReward T n η u'| ^ p) (iidLaw 2 (realLaw ν)) := by
      have hcongr : (fun η : Site 2 → ℝ => |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
            ⌊(n : ℝ) * u' 0⌋ ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
            orientedBoxReward T n η u'| ^ p) =
          (fun η : Site 2 → ℝ => |orientedBoxReward T n η u' -
            orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
              ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p) := by
        funext η
        rw [abs_sub_comm]
      exact hcongr ▸ hcellInt'
    have hnrp : (n : ℝ) ^ (-(p / 4)) ≤ (dist u u') ^ (p / 4) := by
      have h1 : (1 : ℝ) ≤ ((n : ℝ) * dist u u') ^ (p / 4) := Real.one_le_rpow h hp4
      rw [Real.mul_rpow hn0.le dist_nonneg] at h1
      have h2 : (n : ℝ) ^ (-(p / 4)) * (n : ℝ) ^ (p / 4) = 1 := by
        rw [← Real.rpow_add hn0, show -(p / 4) + p / 4 = 0 by ring, Real.rpow_zero]
      calc (n : ℝ) ^ (-(p / 4)) = (n : ℝ) ^ (-(p / 4)) * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) ^ (-(p / 4)) * ((n : ℝ) ^ (p / 4) * (dist u u') ^ (p / 4)) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hn0.le _)
        _ = (dist u u') ^ (p / 4) := by rw [← mul_assoc, h2, one_mul]
    have hpoint : ∀ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p ≤
        3 ^ p * (|orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
              ⌊(n : ℝ) * u 0⌋ ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
              orientedBoxReward T n η u'| ^ p) := by
      intro η
      have e : orientedBoxReward T n η u - orientedBoxReward T n η u' =
          (orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
              ⌊(n : ℝ) * u 0⌋ ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋) +
            (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋) +
            (orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
              orientedBoxReward T n η u') := by ring
      rw [e]
      exact abs_add_add_rpow_le _ _ _ _ hp1
    have hgInt : Integrable (fun η : Site 2 → ℝ =>
        3 ^ p * (|orientedBoxReward T n η u - orientedGridReward n ⌊(n : ℝ) * T⌋₊ η
              ⌊(n : ℝ) * u 0⌋ ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
              orientedBoxReward T n η u'| ^ p)) (iidLaw 2 (realLaw ν)) :=
      ((hcellInt.add hfarInt).add hcellInt3).const_mul _
    have hfMeas : Measurable fun η : Site 2 → ℝ =>
        |orientedBoxReward T n η u - orientedBoxReward T n η u'| ^ p :=
      measurable_abs_rpow ((measurable_orientedBoxReward T n u).sub
        (measurable_orientedBoxReward T n u')) p
    have hfInt : Integrable (fun η : Site 2 → ℝ => |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p) (iidLaw 2 (realLaw ν)) :=
      hgInt.mono' hfMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun η => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
          exact hpoint η)
    refine ⟨hfInt, ?_⟩
    calc ∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
          orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν))
        ≤ ∫ η : Site 2 → ℝ, 3 ^ p * (|orientedBoxReward T n η u -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p +
            |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
              orientedBoxReward T n η u'| ^ p) ∂(iidLaw 2 (realLaw ν)) :=
          integral_mono_ae hfInt hgInt (Filter.Eventually.of_forall hpoint)
      _ = 3 ^ p * ((∫ η : Site 2 → ℝ, |orientedBoxReward T n η u -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) +
            (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u 0⌋
                ⌊Real.sqrt n * u 1 + (n : ℝ) * u 0 / 2⌋ -
              orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋| ^ p ∂(iidLaw 2 (realLaw ν))) +
            (∫ η : Site 2 → ℝ, |orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * u' 0⌋
                ⌊Real.sqrt n * u' 1 + (n : ℝ) * u' 0 / 2⌋ -
              orientedBoxReward T n η u'| ^ p ∂(iidLaw 2 (realLaw ν)))) := by
          rw [integral_const_mul, integral_add, integral_add]
          all_goals first
            | exact hcellInt.add hfarInt
            | exact hcellInt3
            | exact hcellInt
            | exact hfarInt
      _ ≤ 3 ^ p * (Mc * (n : ℝ) ^ (-(p / 4)) + M₁ * (dist u u') ^ (p / 4) +
            Mc * (n : ℝ) ^ (-(p / 4))) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add hcellBound2 hfarBound) hcellBound2')
            (Real.rpow_nonneg (by norm_num) _)
      _ = 3 ^ p * ((2 * Mc) * (n : ℝ) ^ (-(p / 4)) + M₁ * (dist u u') ^ (p / 4)) := by
          ring
      _ ≤ 3 ^ p * ((2 * Mc) * (dist u u') ^ (p / 4) + M₁ * (dist u u') ^ (p / 4)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hnrp
              (mul_nonneg (by norm_num) hMc0)) le_rfl)
            (Real.rpow_nonneg (by norm_num) _)
      _ = (3 ^ p * (2 * Mc + M₁)) * (dist u u') ^ (p / 4) := by ring
      _ ≤ (3 ^ p * (2 * Mc + M₁) + M₂) * (dist u u') ^ (p / 4) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hM₂)
            (Real.rpow_nonneg dist_nonneg _)

end Parking
end
