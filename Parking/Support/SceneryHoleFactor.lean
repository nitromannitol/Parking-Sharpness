import Parking.Support.SceneryHolePartial
import Parking.Support.EscapeGap
import Parking.Support.SquareDeficit

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A dimension-only constant covering ordinary and target scenery reveals. -/
def holeSceneryConst (d : ℕ) : ℝ :=
  max (4 / (1 / (2 * escapeConst d)) ^ 4) (2 / (1 / (2 * escapeConst d)) ^ 2)

def sceneryHoleCost (d : ℕ) (x z v : Site d) : ℝ :=
  holeSceneryConst d * (1 - escapePotential d x v) * (1 - escapePotential d z v)

theorem holeSceneryConst_pos (hd : 3 ≤ d) : 0 < holeSceneryConst d := by
  have hg : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
  apply lt_of_lt_of_le _ (le_max_left _ _)
  positivity

theorem sceneryHoleCost_nonneg (hd : 3 ≤ d) (x z v : Site d) : 0 ≤ sceneryHoleCost d x z v :=
  mul_nonneg (mul_nonneg (holeSceneryConst_pos hd).le (sub_nonneg.mpr (escapePotential_bounds hd x v).2))
    (sub_nonneg.mpr (escapePotential_bounds hd z v).2)

/-- The two-target scenery factor, including reveals at either target. -/
theorem integral_hole_scenery_factor {Ω : Type*} [MeasurableSpace Ω]
    (hd : 3 ≤ d) (μ : Measure Ω) [IsProbabilityMeasure μ] (x z v : Site d) (hxz : x ≠ z)
    (F G : Ω → ℝ) (hF : Measurable F) (hG : Measurable G) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ ω, escapePotential d x v ^ 2 * A ≤ F ω ∧ F ω ≤ A)
    (hg : ∀ ω, escapePotential d z v ^ 2 * B ≤ G ω ∧ G ω ≤ B) :
    (∫ ω, F ω * G ω ∂μ) ≤ Real.exp (sceneryHoleCost d x z v) *
      ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by
  let δ : ℝ := 1 / (2 * escapeConst d)
  have hδ : 0 < δ := by
    dsimp only [δ]
    have hG0 : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
    positivity
  have hfn (ω) := (square_relative_deficit (escapePotential d x v) A (F ω) hA (hf ω).1).1
  have hgn (ω) := (square_relative_deficit (escapePotential d z v) B (G ω) hB (hg ω).1).1
  have hxq : 0 ≤ 1 - escapePotential d x v := sub_nonneg.mpr (escapePotential_bounds hd x v).2
  have hzq : 0 ≤ 1 - escapePotential d z v := sub_nonneg.mpr (escapePotential_bounds hd z v).2
  have hM : 0 ≤ (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ := mul_nonneg (integral_nonneg hfn) (integral_nonneg hgn)
  have htrans (a : ℝ) (ha : a ≤ sceneryHoleCost d x z v)
      (hb : (∫ ω, F ω * G ω ∂μ) ≤ Real.exp a * ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ)) :=
    hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) hM)
  by_cases hvx : v = x
  · have hgap : δ ≤ escapePotential d z v := escapePotential_gap hd (by rw [hvx]; exact hxz)
    have h := integral_square_relative_one_sided μ F G hF hG A B (escapePotential d z v) δ hA hB hδ
      ⟨hgap, (escapePotential_bounds hd z v).2⟩ (fun ω => ⟨hfn ω, (hf ω).2⟩) hg
    apply htrans _ _ h
    have hc := mul_le_mul_of_nonneg_right (le_max_right (4 / δ ^ 4) (2 / δ ^ 2)) hzq
    simpa only [sceneryHoleCost, hvx, escapePotential_self hd, sub_zero, mul_one, holeSceneryConst, δ] using hc
  · by_cases hvz : v = z
    · have hgap : δ ≤ escapePotential d x v := escapePotential_gap hd hvx
      have h := integral_square_relative_one_sided μ G F hG hF B A (escapePotential d x v) δ hB hA hδ
        ⟨hgap, (escapePotential_bounds hd x v).2⟩ (fun ω => ⟨hgn ω, (hg ω).2⟩) hf
      have h' : (∫ ω, F ω * G ω ∂μ) ≤ Real.exp ((2 / δ ^ 2) * (1 - escapePotential d x v)) *
          ((∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ) := by simpa only [mul_comm] using h
      apply htrans _ _ h'
      have hc := mul_le_mul_of_nonneg_right (le_max_right (4 / δ ^ 4) (2 / δ ^ 2)) hxq
      simpa only [sceneryHoleCost, hvz, escapePotential_self hd, sub_zero, mul_one, holeSceneryConst, δ] using hc
    · have h := integral_square_relative_factor μ F G hF hG A B (escapePotential d x v) (escapePotential d z v) δ
        hA hB hδ ⟨escapePotential_gap hd hvx, (escapePotential_bounds hd x v).2⟩
        ⟨escapePotential_gap hd hvz, (escapePotential_bounds hd z v).2⟩ hf hg
      apply htrans _ _ h
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (4 / δ ^ 4) (2 / δ ^ 2)) hxq) hzq

/-- Every partial scenery reveal obeys the same dimension-only two-target factor. -/
theorem scenery_partial_hole_factor (hd : 3 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z v : Site d) (hxz : x ≠ z)
    (S : Set (Site d)) [DecidablePred (· ∈ S)] (η : Site d → ℤ) :
    let f := fun k : ℤ => partialInt (fun _ : Site d => ν) (insert v S)
      (fun ζ => matchedMeanH (clippedField ζ) ρ T x) (Function.update η v k)
    let g := fun k : ℤ => partialInt (fun _ : Site d => ν) (insert v S)
      (fun ζ => matchedMeanH (clippedField ζ) ρ T z) (Function.update η v k)
    (∫ k, f k * g k ∂ν) ≤ Real.exp (sceneryHoleCost d x z v) * ((∫ k, f k ∂ν) * ∫ k, g k ∂ν) := by
  obtain ⟨A, hA, hf⟩ := scenery_partial_hole_relative hd ν ρ T x v S η
  obtain ⟨B, hB, hg⟩ := scenery_partial_hole_relative hd ν ρ T z v S η
  exact integral_hole_scenery_factor hd ν x z v hxz _ _ (measurable_from_countable' _) (measurable_from_countable' _)
    A B hA hB hf hg
end Parking
