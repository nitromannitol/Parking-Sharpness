/-
The covariance limit of the interpolated (continuous) box reward field, upgraded from the
grid-point covariance limit of `Parking.Support.TightCov` via the cell-corner moment bound of
`Parking.Support.TightKolmogorov` (`parking.tex:3192-3203`).

`Parking.tendsto_integral_orientedGridReward_mul_box` (`TightCov.lean`) gives the covariance
limit at the GRID point nearest a real box point, not yet at `Parking.orientedBoxReward`
itself. The gap is closed here by an elementary `L²` perturbation argument: the cell-corner
moment bound `Parking.exists_orientedBoxReward_cell_moment`, read at `p = 2`, shows the
squared `L²` distance between the box reward and its nearest grid value vanishes as `n → ∞`,
so by Cauchy-Schwarz the three extra cross terms of the bilinear expansion
`(G + Δ)(G' + Δ') = GG' + GΔ' + ΔG' + ΔΔ'` vanish and only the grid covariance limit survives.
-/
import Parking.Support.TightCov

open MeasureTheory Filter Topology LatticeProb

noncomputable section
namespace Parking

/-- **A generic `L²` perturbation lemma**: if the squared `L²` norms of `g n` vanish and the
squared `L²` norms of `f n` converge, the cross correlation `∫ f n * g n` vanishes. This is
Cauchy-Schwarz applied along the sequence, with no structure on `f, g` beyond square
integrability. -/
theorem tendsto_integral_mul_of_sq_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : ℕ → Ω → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hfi : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ)
    (hgi : ∀ n, Integrable (fun ω => (g n ω) ^ 2) μ)
    {L : ℝ} (hfsq : Tendsto (fun n => ∫ ω, (f n ω) ^ 2 ∂μ) atTop (𝓝 L))
    (hgsq : Tendsto (fun n => ∫ ω, (g n ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, f n ω * g n ω ∂μ) atTop (𝓝 0) := by
  have hconj : Real.HolderConjugate 2 2 := by constructor <;> norm_num
  have hfmem : ∀ n, MemLp (f n) 2 μ := fun n => (memLp_two_iff_integrable_sq (hfm n)).mpr (hfi n)
  have hgmem : ∀ n, MemLp (g n) 2 μ := fun n => (memLp_two_iff_integrable_sq (hgm n)).mpr (hgi n)
  have hptsq : ∀ h : Ω → ℝ, ∀ ω, ‖h ω‖ ^ (2 : ℝ) = (h ω) ^ 2 := by
    intro h ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have hrpoweq : ∀ h : Ω → ℝ, (∫ ω, ‖h ω‖ ^ (2 : ℝ) ∂μ) = ∫ ω, (h ω) ^ 2 ∂μ := by
    intro h
    simp_rw [hptsq h]
  have hCS : ∀ n : ℕ, ∫ ω, ‖f n ω‖ * ‖g n ω‖ ∂μ ≤
      (∫ ω, ‖f n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ ω, ‖g n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
    fun n => integral_mul_norm_le_Lp_mul_Lq hconj
      (by simpa using hfmem n) (by simpa using hgmem n)
  have hbound : ∀ n, |∫ ω, f n ω * g n ω ∂μ| ≤
      Real.sqrt (∫ ω, (f n ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (g n ω) ^ 2 ∂μ) := by
    intro n
    have habs : ∀ ω, |f n ω * g n ω| = ‖f n ω‖ * ‖g n ω‖ := by
      intro ω; rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    calc |∫ ω, f n ω * g n ω ∂μ| ≤ ∫ ω, |f n ω * g n ω| ∂μ := abs_integral_le_integral_abs
      _ = ∫ ω, ‖f n ω‖ * ‖g n ω‖ ∂μ := by simp_rw [habs]
      _ ≤ (∫ ω, ‖f n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ ω, ‖g n ω‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hCS n
      _ = Real.sqrt (∫ ω, (f n ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (g n ω) ^ 2 ∂μ) := by
          rw [hrpoweq (f n), hrpoweq (g n), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hsqrtf : Tendsto (fun n => Real.sqrt (∫ ω, (f n ω) ^ 2 ∂μ)) atTop (𝓝 (Real.sqrt L)) := by
    have h := (Real.continuous_sqrt.tendsto L).comp hfsq
    simp only [Function.comp_def] at h
    exact h
  have hsqrtg : Tendsto (fun n => Real.sqrt (∫ ω, (g n ω) ^ 2 ∂μ)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hgsq
    simp only [Function.comp_def, Real.sqrt_zero] at h
    exact h
  have hprod : Tendsto (fun n => Real.sqrt (∫ ω, (f n ω) ^ 2 ∂μ) *
      Real.sqrt (∫ ω, (g n ω) ^ 2 ∂μ)) atTop (𝓝 (Real.sqrt L * 0)) := hsqrtf.mul hsqrtg
  rw [mul_zero] at hprod
  refine squeeze_zero_norm (fun n => ?_) hprod
  rw [Real.norm_eq_abs]
  exact hbound n

/-- **The covariance of the interpolated box reward field at two real box points**
converges to `Var(η) · Parking.contOverlap`, upgrading `Parking.tendsto_integral_
orientedGridReward_mul_box` from the nearest grid value to `Parking.orientedBoxReward` itself.
This is Stage 1 of the covariance-to-Gaussian step, at the field the finite-dimensional
characteristic-function bridge (`Parking.Support.TightLinear`) actually reads. -/
theorem tendsto_integral_orientedBoxReward_mul (ν : Measure ℤ) (hν : CriticalLaw ν)
    (hBinomial : External.BinomialLocalCLT) (T : ℝ)
    (u u' : Fin 2 → ℝ) (hu0 : 0 ≤ u 0) (huT : u 0 ≤ T) (hu'0 : 0 ≤ u' 0) (hu'T : u' 0 ≤ T) :
    Tendsto (fun n : ℕ => ∫ η : Site 2 → ℝ,
        orientedBoxReward T n η u * orientedBoxReward T n η u'
      ∂(iidLaw 2 (realLaw ν))) atTop
      (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T u u')) := by
  haveI := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  set μ := iidLaw 2 (realLaw ν) with hμ
  set G : (Fin 2 → ℝ) → ℕ → (Site 2 → ℝ) → ℝ := fun v n η =>
    orientedGridReward n ⌊(n : ℝ) * T⌋₊ η ⌊(n : ℝ) * v 0⌋
      ⌊Real.sqrt n * v 1 + (n : ℝ) * v 0 / 2⌋ with hGdef
  set Δ : (Fin 2 → ℝ) → ℕ → (Site 2 → ℝ) → ℝ := fun v n η =>
    orientedBoxReward T n η v - G v n η with hΔdef
  obtain ⟨C, _hC, hcell⟩ := exists_orientedBoxReward_cell_moment ν hν 2 (by norm_num)
  obtain ⟨C2, _hC2, hsingle⟩ := exists_orientedGridReward_single_moment ν hν 2 (by norm_num)
  have hptsq : ∀ x : ℝ, |x| ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have hGmeas : ∀ v : Fin 2 → ℝ, ∀ n, Measurable (G v n) := fun v n =>
    measurable_orientedGridReward n ⌊(n : ℝ) * T⌋₊ ⌊(n : ℝ) * v 0⌋
      ⌊Real.sqrt n * v 1 + (n : ℝ) * v 0 / 2⌋
  have hΔmeas : ∀ v : Fin 2 → ℝ, ∀ n, Measurable (Δ v n) := fun v n =>
    (measurable_orientedBoxReward T n v).sub (hGmeas v n)
  have hGsqint : ∀ v : Fin 2 → ℝ, ∀ n : ℕ, Integrable (fun η => (G v n η) ^ 2) μ := by
    intro v n
    refine (hsingle n ⌊(n : ℝ) * T⌋₊ ⌊(n : ℝ) * v 0⌋
      ⌊Real.sqrt n * v 1 + (n : ℝ) * v 0 / 2⌋).1.congr
      (Filter.Eventually.of_forall fun η => ?_)
    exact hptsq (G v n η)
  have hΔsqint : ∀ v : Fin 2 → ℝ, 0 ≤ v 0 → ∀ n : ℕ,
      Integrable (fun η => (Δ v n η) ^ 2) μ := by
    intro v hv0 n
    refine (hcell T n v hv0).1.congr (Filter.Eventually.of_forall fun η => ?_)
    exact hptsq (Δ v n η)
  have hΔsqtendsto : ∀ v : Fin 2 → ℝ, 0 ≤ v 0 →
      Tendsto (fun n => ∫ η, (Δ v n η) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro v hv0
    have hbound : ∀ n : ℕ, ∫ η, (Δ v n η) ^ 2 ∂μ ≤
        4 ^ ((2 : ℝ) + 1) * ((C * 5) ^ ((2 : ℝ) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 4))) := by
      intro n
      calc ∫ η, (Δ v n η) ^ 2 ∂μ = ∫ η, |Δ v n η| ^ (2 : ℝ) ∂μ :=
            integral_congr_ae (Filter.Eventually.of_forall fun η => (hptsq (Δ v n η)).symm)
        _ ≤ 4 ^ ((2 : ℝ) + 1) * ((C * 5) ^ ((2 : ℝ) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 4))) :=
            (hcell T n v hv0).2
    have hnn : ∀ n : ℕ, 0 ≤ ∫ η, (Δ v n η) ^ 2 ∂μ :=
      fun n => integral_nonneg fun η => sq_nonneg _
    have hlim : Tendsto (fun n : ℕ =>
        4 ^ ((2 : ℝ) + 1) * ((C * 5) ^ ((2 : ℝ) / 2) * (n : ℝ) ^ (-((2 : ℝ) / 4))))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-((2 : ℝ) / 4))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (y := (2 : ℝ) / 4) (by norm_num)).comp
          tendsto_natCast_atTop_atTop
      have := (h0.const_mul ((C * 5) ^ ((2 : ℝ) / 2))).const_mul ((4 : ℝ) ^ ((2 : ℝ) + 1))
      simpa using this
    exact squeeze_zero hnn hbound hlim
  have hGtendsto : ∀ v v' : Fin 2 → ℝ, 0 ≤ v 0 → v 0 ≤ T → 0 ≤ v' 0 → v' 0 ≤ T →
      Tendsto (fun n => ∫ η, G v n η * G v' n η ∂μ) atTop
        (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T v v')) :=
    fun v v' hv0 hvT hv'0 hv'T =>
      tendsto_integral_orientedGridReward_mul_box ν hν hBinomial T v v' hv0 hvT hv'0 hv'T
  have hGsqtendsto : ∀ v : Fin 2 → ℝ, 0 ≤ v 0 → v 0 ≤ T →
      Tendsto (fun n => ∫ η, (G v n η) ^ 2 ∂μ) atTop
        (𝓝 ((∫ x : ℝ, x ^ 2 ∂(realLaw ν)) * contOverlap T v v)) := by
    intro v hv0 hvT
    refine (hGtendsto v v hv0 hvT hv0 hvT).congr' (Filter.Eventually.of_forall fun n => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  -- the three cross terms of the bilinear expansion vanish
  have hcrossGD : Tendsto (fun n => ∫ η, G u n η * Δ u' n η ∂μ) atTop (𝓝 0) :=
    tendsto_integral_mul_of_sq_tendsto_zero (fun n => (hGmeas u n).aestronglyMeasurable)
      (fun n => (hΔmeas u' n).aestronglyMeasurable) (fun n => hGsqint u n)
      (fun n => hΔsqint u' hu'0 n) (hGsqtendsto u hu0 huT) (hΔsqtendsto u' hu'0)
  have hcrossDG : Tendsto (fun n => ∫ η, Δ u n η * G u' n η ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_mul_of_sq_tendsto_zero
      (fun n => (hGmeas u' n).aestronglyMeasurable)
      (fun n => (hΔmeas u n).aestronglyMeasurable) (fun n => hGsqint u' n)
      (fun n => hΔsqint u hu0 n) (hGsqtendsto u' hu'0 hu'T) (hΔsqtendsto u hu0)
    refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => mul_comm _ _)
  have hcrossDD : Tendsto (fun n => ∫ η, Δ u n η * Δ u' n η ∂μ) atTop (𝓝 0) :=
    tendsto_integral_mul_of_sq_tendsto_zero (fun n => (hΔmeas u n).aestronglyMeasurable)
      (fun n => (hΔmeas u' n).aestronglyMeasurable) (fun n => hΔsqint u hu0 n)
      (fun n => hΔsqint u' hu'0 n) (hΔsqtendsto u hu0) (hΔsqtendsto u' hu'0)
  have hGint : ∀ v : Fin 2 → ℝ, ∀ n, MemLp (G v n) 2 μ :=
    fun v n => (memLp_two_iff_integrable_sq (hGmeas v n).aestronglyMeasurable).mpr (hGsqint v n)
  have hΔint : ∀ v : Fin 2 → ℝ, 0 ≤ v 0 → ∀ n, MemLp (Δ v n) 2 μ :=
    fun v hv0 n => (memLp_two_iff_integrable_sq (hΔmeas v n).aestronglyMeasurable).mpr
      (hΔsqint v hv0 n)
  have hsplit : ∀ n : ℕ, ∫ η, orientedBoxReward T n η u * orientedBoxReward T n η u' ∂μ =
      (∫ η, G u n η * G u' n η ∂μ) + (∫ η, G u n η * Δ u' n η ∂μ) +
        (∫ η, Δ u n η * G u' n η ∂μ) + (∫ η, Δ u n η * Δ u' n η ∂μ) := by
    intro n
    have hpt : ∀ η, orientedBoxReward T n η u * orientedBoxReward T n η u' =
        G u n η * G u' n η + G u n η * Δ u' n η + Δ u n η * G u' n η + Δ u n η * Δ u' n η := by
      intro η
      show orientedBoxReward T n η u * orientedBoxReward T n η u' =
          G u n η * G u' n η + G u n η * (orientedBoxReward T n η u' - G u' n η) +
            (orientedBoxReward T n η u - G u n η) * G u' n η +
            (orientedBoxReward T n η u - G u n η) * (orientedBoxReward T n η u' - G u' n η)
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [integral_add, integral_add, integral_add]
    · exact (hGint u n).integrable_mul (hGint u' n)
    · exact (hGint u n).integrable_mul (hΔint u' hu'0 n)
    · refine ((hGint u n).integrable_mul (hGint u' n)).add
        ((hGint u n).integrable_mul (hΔint u' hu'0 n))
    · exact (hΔint u hu0 n).integrable_mul (hGint u' n)
    · refine (((hGint u n).integrable_mul (hGint u' n)).add
        ((hGint u n).integrable_mul (hΔint u' hu'0 n))).add
        ((hΔint u hu0 n).integrable_mul (hGint u' n))
    · exact (hΔint u hu0 n).integrable_mul (hΔint u' hu'0 n)
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => (hsplit n).symm) ?_
  have h1 := ((hGtendsto u u' hu0 huT hu'0 hu'T).add hcrossGD).add hcrossDG
  have h2 := h1.add hcrossDD
  simpa using h2

end Parking
end
