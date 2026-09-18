/- Exact integration over the cells of the parabolic lattice. -/
import Parking.Support.SpatialTestedSum
import Parking.Generic.TimeCell

open MeasureTheory LatticeProb Set
noncomputable section
namespace Parking
variable {d : ℕ}

theorem integrable_gridFn_of_support_bound {φ : (Fin d → ℝ) → ℝ} {B R : ℝ}
    (hB : 0 < B) (hb : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) :
    Integrable (gridFn φ R) := by
  have he := funext (gridFn_eq_sum_indicator hB hb hR)
  rw [he]
  apply integrable_finsetSum
  intro y _
  apply (integrable_indicator_iff (latticeCube_measurableSet y R)).mpr
  refine integrableOn_const ?_
  rw [volume_latticeCube y (lt_of_lt_of_le one_pos hR)]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem integrable_barDivisible_mul_gridFn (w : Data d) (s : ℝ)
    {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hb : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) :
    Integrable (fun x => barDivisible w R s x * gridFn φ R x) := by
  have hRne : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  let f : (Fin d → ℝ) → ℝ := fun x => barDivisible w R s x * φ x
  have hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ B := fun x hx =>
    hb x (fun hz => hx (by simp [f, hz]))
  have he : gridFn f R = fun x => barDivisible w R s x * gridFn φ R x := by
    funext x
    simp only [gridFn, f, barDivisible, latticePoint_rescale _ hRne]
    rfl
  rw [← he]
  exact integrable_gridFn_of_support_bound hB hf hR

theorem integrable_barDivisible_mul_scaledWalkTest (w : Data d) (s : ℝ)
    {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hb : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) :
    Integrable (fun x => barDivisible w R s x * scaledWalkTest φ R x) := by
  have hRne : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  have hb' : ∀ x, scaledWalkTest φ R x ≠ 0 → ‖x‖ ≤ B + 2 := by
    intro x hx
    by_contra hn
    exact hx (scaledWalkTest_eq_zero_of_norm_gt hb hR (lt_of_not_ge hn))
  have hg : gridFn (scaledWalkTest φ R) R = scaledWalkTest φ R := by
    funext x
    simp only [gridFn, scaledWalkTest, latticePoint_rescale _ hRne]
    rfl
  rw [← hg]
  exact integrable_barDivisible_mul_gridFn w s (by linarith : 0 < B + 2) hb' hR

/-- The time-strip restriction of a parabolic cell function is a finite step function. -/
theorem parabolic_strip_eq_step (f : ℕ → (Fin d → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ) :
    ({p : ℝ × (Fin d → ℝ) | p.1 ∈ Ico 0 ((N : ℝ) / R ^ 2)}.indicator
      (fun p => f ⌊p.1 * R ^ 2⌋₊ p.2)) =
        fun p => Generic.TimeCell.step (1 / R ^ 2) N (fun n => f n p.2) p.1 := by
  classical
  funext p
  rw [Generic.TimeCell.step_eq_indicator (by positivity : 0 < 1 / R ^ 2)]
  simp only [div_eq_mul_inv, one_mul, inv_inv, Set.indicator, Set.mem_setOf_eq]

/-- Exact integration of a parabolic cell function over a finite time strip. -/
theorem integral_parabolic_strip (f : ℕ → (Fin d → ℝ) → ℝ)
    {R : ℝ} (hR : 0 < R) (N : ℕ) (hf : ∀ n < N, Integrable (f n)) :
    (∫ p : ℝ × (Fin d → ℝ) in {p | p.1 ∈ Ico 0 ((N : ℝ) / R ^ 2)},
      f ⌊p.1 * R ^ 2⌋₊ p.2) = (1 / R ^ 2) * ∑ n ∈ Finset.range N, ∫ x, f n x := by
  have hm : MeasurableSet {p : ℝ × (Fin d → ℝ) | p.1 ∈ Ico 0 ((N : ℝ) / R ^ 2)} :=
    measurableSet_Ico.preimage measurable_fst
  rw [← integral_indicator hm,
    parabolic_strip_eq_step f hR N]
  exact Generic.TimeCell.integral_step_prod volume (by positivity) N f hf

/-- Testing the rescaled recursion is exactly integration against its parabolic coefficients. -/
theorem barDivisible_tested_parabolic_integral (w : Data d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) (T : ℝ)
    {R : ℝ} (hR : 1 ≤ R) (hzero : ∀ x, ψ (0, x) = 0)
    (hfinal : ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0)
    (hpos : tsupport ψ ⊆ {p | 0 < barDivisible w R p.1 p.2}) :
    -(∫ p : ℝ × (Fin d → ℝ) in {p | p.1 ∈ Ico 0 ((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2)},
      barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p) =
      (∫ p : ℝ × (Fin d → ℝ) in {p | p.1 ∈ Ico 0 ((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2)},
        barDivisible w R p.1 p.2 * parabolicSpaceTest ψ R p) +
        scenePair w R (sampledTimeIntegral ψ T R) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  let f : ℕ → (Fin d → ℝ) → ℝ := fun n x => barDivisible w R ((n : ℝ) / R ^ 2) x *
    gridFn (fun x => R ^ 2 * (ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x) -
      ψ (((n : ℝ) / R ^ 2), x))) R x
  let g : ℕ → (Fin d → ℝ) → ℝ := fun n x => barDivisible w R ((n : ℝ) / R ^ 2) x *
    scaledWalkTest (fun x => ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x)) R x
  obtain ⟨B, hB⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × (Fin d → ℝ) => p.2) continuous_snd.continuousOn
  have hbound : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ max B 1 :=
    fun s x hx => (hB (s, x) (subset_tsupport ψ hx)).trans (le_max_left _ _)
  have hb : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hf : ∀ n, Integrable (f n) := by
    intro n
    apply integrable_barDivisible_mul_gridFn w _ hb _ hR
    intro x hx
    by_cases ha : ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x) = 0
    · apply hbound _ x
      intro hz
      exact hx (by rw [ha, hz]; ring)
    · exact hbound _ x ha
  have hg : ∀ n, Integrable (g n) := fun n =>
    integrable_barDivisible_mul_scaledWalkTest w _ hb (hbound _) hR
  have htime : ∀ s : ℝ, ((⌊s * R ^ 2⌋₊ + 1 : ℕ) : ℝ) / R ^ 2 =
      parabolicTime R s + 1 / R ^ 2 := by intro s; simp [parabolicTime, add_div]
  have hval : ∀ s x, barDivisible w R ((⌊s * R ^ 2⌋₊ : ℝ) / R ^ 2) x =
      barDivisible w R s x := by
    intro s x
    simp only [barDivisible, div_mul_cancel₀ _ (pow_ne_zero _ hRpos.ne'), Nat.floor_natCast]
  have heF : (fun p : ℝ × (Fin d → ℝ) => f ⌊p.1 * R ^ 2⌋₊ p.2) =
      fun p => barDivisible w R p.1 p.2 * parabolicTimeTest ψ R p := by
    funext p
    simp only [f, hval, gridFn, htime, parabolicTimeTest, parabolicTime, latticePoint]
  have heG : (fun p : ℝ × (Fin d → ℝ) => g ⌊p.1 * R ^ 2⌋₊ p.2) =
      fun p => barDivisible w R p.1 p.2 * parabolicSpaceTest ψ R p := by
    funext p
    simp only [g, hval, htime, parabolicSpaceTest]
  rw [← heF, ← heG, integral_parabolic_strip f hRpos _ (fun n _ => hf n),
    integral_parabolic_strip g hRpos _ (fun n _ => hg n)]
  have he := barDivisible_tested_spaceTime_spatial_integrals w hψ T hR hzero hfinal hpos
  change -(1 / R ^ 2) * (∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊, ∫ x, f n x) =
    scenePair w R (sampledTimeIntegral ψ T R) +
      (1 / R ^ 2) * (∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊, ∫ x, g n x) at he
  linarith

end Parking
