/- Spatial integration of the weak recursion on the parabolic mesh. -/
import Parking.Support.SpatialParabolicTest
import Parking.Support.SpatialTimeSourceApproximation

open MeasureTheory LatticeProb Set
noncomputable section
namespace Parking
variable {d : ℕ}

/-- Compactly supported spatial tests have finite support after sampling. -/
theorem hasFiniteSupport_sampledTest {φ : (Fin d → ℝ) → ℝ} (hφ : HasCompactSupport φ)
    {R : ℝ} (hR : 1 ≤ R) :
    Function.HasFiniteSupport (fun y : Site d => φ (fun i => (y i : ℝ) / R)) := by
  obtain ⟨B, hB, hb⟩ := exists_norm_bound_of_hasCompactSupport hφ
  exact (sceneryBox d B R).finite_toSet.subset
    (fun y hy => mem_sceneryBox_of_ne_zero hB hb hR hy)

/-- Integrating a sampled coefficient against the rescaled field is an exact lattice sum. -/
theorem integral_barDivisible_mul_gridFn (w : Data d) (s : ℝ)
    {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hb : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) :
    (∫ x, barDivisible w R s x * gridFn φ R x) =
      (∑' y : Site d, barDivisible w R s (fun i => (y i : ℝ) / R) *
        φ (fun i => (y i : ℝ) / R)) * (1 / R) ^ d := by
  have hRne : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  let f : (Fin d → ℝ) → ℝ := fun x => barDivisible w R s x * φ x
  have hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ B := fun x hx =>
    hb x (fun hz => hx (by simp [f, hz]))
  have he : gridFn f R = fun x => barDivisible w R s x * gridFn φ R x := by
    funext x
    simp only [gridFn, f, barDivisible, latticePoint_rescale _ hRne]
    rfl
  rw [← he]
  exact integral_gridFn_eq_latticeSum hB hf hR

/-- The spatial generator has the same exact cell integration formula. -/
theorem integral_barDivisible_mul_scaledWalkTest (w : Data d) (s : ℝ)
    {φ : (Fin d → ℝ) → ℝ} {B R : ℝ} (hB : 0 < B)
    (hb : ∀ x, φ x ≠ 0 → ‖x‖ ≤ B) (hR : 1 ≤ R) :
    (∫ x, barDivisible w R s x * scaledWalkTest φ R x) =
      (∑' y : Site d, barDivisible w R s (fun i => (y i : ℝ) / R) *
        (R ^ 2 * (walkOp (fun z => φ (fun i => (z i : ℝ) / R)) y -
          φ (fun i => (y i : ℝ) / R)))) * (1 / R) ^ d := by
  have hRne : R ≠ 0 := (lt_of_lt_of_le one_pos hR).ne'
  have hb' : ∀ x, scaledWalkTest φ R x ≠ 0 → ‖x‖ ≤ B + 2 := by
    intro x hx
    by_contra hn
    exact hx (scaledWalkTest_eq_zero_of_norm_gt hb hR (lt_of_not_ge hn))
  have hg : gridFn (scaledWalkTest φ R) R = scaledWalkTest φ R := by
    funext x
    simp only [gridFn, scaledWalkTest, latticePoint_rescale _ hRne]
    rfl
  have he := integral_barDivisible_mul_gridFn w s (by linarith : 0 < B + 2) hb' hR
  rw [hg] at he
  simpa only [scaledWalkTest_rescale _ _ hRne] using he

/-- The sampled source is the time sum of the lattice scenery pairings. -/
theorem scenePair_sampledTimeIntegral (w : Data d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) (T : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    scenePair w R (sampledTimeIntegral ψ T R) =
      (R ^ (-(d : ℝ) / 2) / R ^ 2) *
        ∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊, ∑' y : Site d,
          ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), fun i => (y i : ℝ) / R) * (w.1 y : ℝ) := by
  have hs : ∀ n : ℕ, Summable (fun y : Site d =>
      ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), fun i => (y i : ℝ) / R) * (w.1 y : ℝ)) :=
    fun n => summable_of_hasFiniteSupport ((hasFiniteSupport_sampledTest
      (isTestFun_spaceSlice hψ _).2 hR).mul_left _)
  unfold scenePair sampledTimeIntegral
  have he : ∀ y : Site d,
      (w.1 y : ℝ) * ((1 / R ^ 2) * ∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊,
        ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), fun i => (y i : ℝ) / R)) =
      (1 / R ^ 2) * ∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊,
        ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), fun i => (y i : ℝ) / R) * (w.1 y : ℝ) := by
    intro y
    rw [← Finset.sum_mul]
    ring
  simp_rw [he]
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun n _ => hs n)]
  ring

/-- The recursion integrated spatially, with exact parabolic cell weights. -/
theorem barDivisible_tested_spaceTime_spatial_integrals (w : Data d)
    {ψ : ℝ × (Fin d → ℝ) → ℝ} (hψ : IsSpaceTimeTest ψ) (T : ℝ)
    {R : ℝ} (hR : 1 ≤ R)
    (hzero : ∀ x, ψ (0, x) = 0)
    (hfinal : ∀ x, ψ (((⌈T * R ^ 2⌉₊ : ℝ) / R ^ 2), x) = 0)
    (hpos : tsupport ψ ⊆ {p | 0 < barDivisible w R p.1 p.2}) :
    -(1 / R ^ 2) * (∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊,
      ∫ x, barDivisible w R ((n : ℝ) / R ^ 2) x *
        gridFn (fun x => R ^ 2 * (ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x) -
          ψ (((n : ℝ) / R ^ 2), x))) R x) =
      scenePair w R (sampledTimeIntegral ψ T R) +
        (1 / R ^ 2) * (∑ n ∈ Finset.range ⌈T * R ^ 2⌉₊,
          ∫ x, barDivisible w R ((n : ℝ) / R ^ 2) x *
            scaledWalkTest (fun x => ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x)) R x) := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  let θ : ℕ → Site d → ℝ := fun n y => ψ (((n : ℝ) / R ^ 2), fun i => (y i : ℝ) / R)
  have hθ : ∀ n, Function.HasFiniteSupport (θ n) := fun n =>
    hasFiniteSupport_sampledTest (isTestFun_spaceSlice hψ _).2 hR
  have heq := barDivisible_tested_spaceTime w hRpos ⌈T * R ^ 2⌉₊ θ hθ
    (by simpa [θ] using fun y : Site d => hzero (fun i => (y i : ℝ) / R))
    (fun y => hfinal _) (fun n _ y hy => hpos (subset_tsupport ψ hy))
  obtain ⟨B, hB⟩ := hψ.2.1.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × (Fin d → ℝ) => p.2) continuous_snd.continuousOn
  have hbound : ∀ s x, ψ (s, x) ≠ 0 → ‖x‖ ≤ max B 1 :=
    fun s x hx => (hB (s, x) (subset_tsupport ψ hx)).trans (le_max_left _ _)
  have hb : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hleft : ∀ n : ℕ, (∫ x, barDivisible w R ((n : ℝ) / R ^ 2) x *
      gridFn (fun x => R ^ 2 * (ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x) -
        ψ (((n : ℝ) / R ^ 2), x))) R x) =
      (∑' y : Site d, barDivisible w R ((n : ℝ) / R ^ 2) (fun i => (y i : ℝ) / R) *
        (R ^ 2 * (θ (n + 1) y - θ n y))) * (1 / R) ^ d := by
    intro n
    apply integral_barDivisible_mul_gridFn w _ hb _ hR
    intro x hx
    by_cases ha : ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x) = 0
    · apply hbound _ x
      intro hz
      exact hx (by rw [ha, hz]; ring)
    · exact hbound _ x ha
  have hright : ∀ n : ℕ, (∫ x, barDivisible w R ((n : ℝ) / R ^ 2) x *
      scaledWalkTest (fun x => ψ ((((n + 1 : ℕ) : ℝ) / R ^ 2), x)) R x) =
      (∑' y : Site d, (R ^ 2 * (walkOp (θ (n + 1)) y - θ (n + 1) y)) *
        barDivisible w R ((n : ℝ) / R ^ 2) (fun i => (y i : ℝ) / R)) * (1 / R) ^ d := by
    intro n
    rw [integral_barDivisible_mul_scaledWalkTest w _ hb (hbound _) hR]
    congr 1
    apply tsum_congr
    intro y
    exact mul_comm _ _
  simp_rw [hleft, hright]
  rw [← Finset.sum_mul, ← Finset.sum_mul, scenePair_sampledTimeIntegral w hψ T hR]
  have hscale : (1 / R ^ 2) * (1 / R) ^ d * R ^ ((d : ℝ) / 2) =
      R ^ (-(d : ℝ) / 2) / R ^ 2 := by
    have he : (1 / R) ^ d * R ^ ((d : ℝ) / 2) = R ^ (-(d : ℝ) / 2) := by
      rw [one_div_pow, one_div, ← Real.rpow_natCast R d, ← Real.rpow_neg hRpos.le,
        ← Real.rpow_add hRpos]
      congr 1
      ring
    rw [mul_assoc, he]
    ring
  have hh := congrArg (fun a : ℝ => ((1 / R ^ 2) * (1 / R) ^ d) * a) heq
  dsimp only [θ] at hh ⊢
  simp only [mul_add, ← mul_assoc] at hh
  rw [hscale] at hh
  simp only [← mul_assoc]
  linear_combination hh

end Parking
