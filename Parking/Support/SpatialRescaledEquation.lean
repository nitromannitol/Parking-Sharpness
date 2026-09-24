/- The divisible recursion at the parabolic scale, before weak testing. -/
import Parking.Support.SpatialDiscreteEquation
import Parking.Support.Continuum
import Parking.Support.LinPotential
import Parking.Support.SpatWWalkGrid

open LatticeProb
noncomputable section
namespace Parking
variable {d : ℕ}

theorem latticePoint_add_rescaled (x : Fin d → ℝ) (z : Site d)
    {R : ℝ} (hR : R ≠ 0) :
    latticePoint R (fun i => x i + (z i : ℝ) / R) = latticePoint R x + z := by
  funext i
  change ⌊R * (x i + (z i : ℝ) / R)⌋ = ⌊R * x i⌋ + z i
  rw [mul_add, mul_div_cancel₀ _ hR, Int.floor_add_intCast]

/-- One continuum time step advances the discrete horizon by exactly one. -/
theorem parabolic_floor_next {R s : ℝ} (hR : R ≠ 0) (hs : 0 ≤ s) :
    ⌊(s + 1 / R ^ 2) * R ^ 2⌋₊ = ⌊s * R ^ 2⌋₊ + 1 := by
  rw [add_mul, one_div_mul_cancel (pow_ne_zero _ hR)]
  exact Nat.floor_add_one (mul_nonneg hs (sq_nonneg R))

/-- The rescaled recursion has the expected noise normalization and generator
coefficient wherever the next rescaled odometer is positive. -/
theorem barDivisible_increment_eq_of_pos (w : Data d)
    {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (x : Fin d → ℝ)
    (hpos : 0 < barDivisible w R (s + 1 / R ^ 2) x) :
    R ^ 2 * (barDivisible w R (s + 1 / R ^ 2) x - barDivisible w R s x) =
      R ^ ((d : ℝ) / 2) * (w.1 (latticePoint R x) : ℝ) +
        R ^ 2 * (walkOp (fun y : Site d => R ^ ((d : ℝ) / 2 - 2) *
          uOf w ⌊s * R ^ 2⌋₊ y) (latticePoint R x) - barDivisible w R s x) := by
  have hc : 0 < R ^ ((d : ℝ) / 2 - 2) := Real.rpow_pos_of_pos hR _
  have hp : 0 < uOf w (⌊s * R ^ 2⌋₊ + 1) (latticePoint R x) := by
    simpa only [barDivisible, parabolic_floor_next hR.ne' hs,
      mul_pos_iff_of_pos_left hc] using hpos
  have heq := divisible_increment_eq_of_pos (fun y => (w.1 y : ℝ))
    ⌊s * R ^ 2⌋₊ (latticePoint R x) hp
  have hscale : R ^ 2 * R ^ ((d : ℝ) / 2 - 2) = R ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR]
    congr 1
    ring
  simp only [barDivisible, parabolic_floor_next hR.ne' hs, walkOp_const_mul]
  have hh := congrArg (fun a : ℝ => R ^ 2 * R ^ ((d : ℝ) / 2 - 2) * a) heq
  change R ^ 2 * (R ^ ((d : ℝ) / 2 - 2) * uOf w (⌊s * R ^ 2⌋₊ + 1) (latticePoint R x) -
    R ^ ((d : ℝ) / 2 - 2) * uOf w ⌊s * R ^ 2⌋₊ (latticePoint R x)) = _
  change R ^ 2 * R ^ ((d : ℝ) / 2 - 2) *
      (uOf w (⌊s * R ^ 2⌋₊ + 1) (latticePoint R x) - uOf w ⌊s * R ^ 2⌋₊ (latticePoint R x)) =
      R ^ 2 * R ^ ((d : ℝ) / 2 - 2) *
        ((w.1 (latticePoint R x) : ℝ) + walkOp (uOf w ⌊s * R ^ 2⌋₊) (latticePoint R x) -
          uOf w ⌊s * R ^ 2⌋₊ (latticePoint R x)) at hh
  rw [← hscale]
  nlinarith [hh]

/-- The rescaled field agrees exactly with its defining values on the parabolic grid. -/
theorem barDivisible_grid (w : Data d) {R : ℝ} (hR : R ≠ 0)
    (n : ℕ) (y : Site d) :
    barDivisible w R ((n : ℝ) / R ^ 2) (fun i => (y i : ℝ) / R) =
      R ^ ((d : ℝ) / 2 - 2) * uOf w n y := by
  simp only [barDivisible, div_mul_cancel₀ _ (pow_ne_zero _ hR), Nat.floor_natCast,
    latticePoint_rescale y hR]

/-- The exact tested equation on the parabolic grid, before multiplication by the
space-time cell volume. Both time boundary terms vanish. -/
theorem barDivisible_tested_spaceTime (w : Data d) {R : ℝ} (hR : 0 < R) (N : ℕ)
    (ψ : ℕ → Site d → ℝ) (hψ : ∀ n, Function.HasFiniteSupport (ψ n))
    (hzero : ∀ x, ψ 0 x = 0) (hfinal : ∀ x, ψ N x = 0)
    (hpos : ∀ n < N, ∀ x, ψ (n + 1) x ≠ 0 →
      0 < barDivisible w R (((n + 1 : ℕ) : ℝ) / R ^ 2)
        (fun i => (x i : ℝ) / R)) :
    -(∑ n ∈ Finset.range N, ∑' x : Site d,
      barDivisible w R ((n : ℝ) / R ^ 2) (fun i => (x i : ℝ) / R) *
        (R ^ 2 * (ψ (n + 1) x - ψ n x))) =
      R ^ ((d : ℝ) / 2) * (∑ n ∈ Finset.range N, ∑' x : Site d,
        ψ (n + 1) x * (w.1 x : ℝ)) +
      ∑ n ∈ Finset.range N, ∑' x : Site d,
        (R ^ 2 * (walkOp (ψ (n + 1)) x - ψ (n + 1) x)) *
          barDivisible w R ((n : ℝ) / R ^ 2) (fun i => (x i : ℝ) / R) := by
  have hc : 0 < R ^ ((d : ℝ) / 2 - 2) := Real.rpow_pos_of_pos hR _
  have hp : ∀ n < N, ∀ x, ψ (n + 1) x ≠ 0 → 0 < uOf w (n + 1) x := by
    intro n hn x hx
    simpa only [barDivisible_grid w hR.ne', mul_pos_iff_of_pos_left hc] using hpos n hn x hx
  have heq := divisible_tested_spaceTime (fun y => (w.1 y : ℝ)) N ψ hψ hzero hfinal hp
  have hscale : R ^ 2 * R ^ ((d : ℝ) / 2 - 2) = R ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR]
    congr 1
    ring
  simp only [barDivisible_grid w hR.ne']
  have hleft : ∀ n x,
      R ^ ((d : ℝ) / 2 - 2) * uOf w n x * (R ^ 2 * (ψ (n + 1) x - ψ n x)) =
      R ^ ((d : ℝ) / 2) * (uOf w n x * (ψ (n + 1) x - ψ n x)) := by
    intro n x
    rw [← hscale]
    ring
  have hright : ∀ n x,
      (R ^ 2 * (walkOp (ψ (n + 1)) x - ψ (n + 1) x)) *
        (R ^ ((d : ℝ) / 2 - 2) * uOf w n x) =
      R ^ ((d : ℝ) / 2) * ((walkOp (ψ (n + 1)) x - ψ (n + 1) x) * uOf w n x) := by
    intro n x
    rw [← hscale]
    ring
  simp only [hleft, hright, tsum_mul_left, ← Finset.mul_sum]
  have hh := congrArg (fun a : ℝ => R ^ ((d : ℝ) / 2) * a) heq
  change R ^ ((d : ℝ) / 2) *
    (-(∑ n ∈ Finset.range N, ∑' x : Site d, uOf w n x * (ψ (n + 1) x - ψ n x))) =
    R ^ ((d : ℝ) / 2) * _ at hh
  rw [mul_neg, mul_add] at hh
  exact hh

end Parking
