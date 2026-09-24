import Parking.Support.SceneryHoleFactor
import Parking.Support.HoleLocality
import Parking.Support.ProductFactor

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- A scenery reveal multiplies the conditional hole product by its prescribed factor. -/
theorem scenery_hole_reveal_section (hd : 3 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z : Site d) (hxz : x ≠ z) (S : Finset (Site d))
    (v : Site d) (hv : v ∉ S) (η : Site d → ℤ) :
    (∫ k, partialInt (fun _ : Site d => ν) (↑(insert v S) : Set (Site d))
      (fun ζ => matchedMeanH (clippedField ζ) ρ T x) (Function.update η v k) *
      partialInt (fun _ : Site d => ν) (↑(insert v S) : Set (Site d))
      (fun ζ => matchedMeanH (clippedField ζ) ρ T z) (Function.update η v k) ∂ν) ≤
      Real.exp (sceneryHoleCost d x z v) *
        (partialInt (fun _ : Site d => ν) (↑S : Set (Site d)) (fun ζ => matchedMeanH (clippedField ζ) ρ T x) η *
        partialInt (fun _ : Site d => ν) (↑S : Set (Site d)) (fun ζ => matchedMeanH (clippedField ζ) ρ T z) η) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hm (y : Site d) : Measurable (fun ζ : Site d → ℤ => matchedMeanH (clippedField ζ) ρ T y) :=
    (measurable_matchedMeanH hd1 ρ T y).comp measurable_clippedField
  have hb (y : Site d) (ζ : Site d → ℤ) : |matchedMeanH (clippedField ζ) ρ T y| ≤ 1 := by
    rw [abs_of_nonneg (clippedMeanH_bounds hd1 ζ ρ T y).1]
    exact (clippedMeanH_bounds hd1 ζ ρ T y).2
  have he (y : Site d) := partialInt_insert_coordinate (fun _ : Site d => ν) (↑S : Set (Site d)) v hv
    (fun ζ => matchedMeanH (clippedField ζ) ρ T y) (hm y) 1 (hb y) η
  have h := scenery_partial_hole_factor hd ν ρ T x z v hxz (↑S : Set (Site d)) η
  dsimp only at h
  rw [← he x, ← he z] at h
  simpa only [Finset.coe_insert] using h

/-- The initial-field factors accumulate over a finite propagation box. -/
theorem scenery_hole_product_factor (hd : 3 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x z u : Site d) (hxz : x ≠ z) (R : ℕ)
    (hxR : boxFinset x T ⊆ boxFinset u R) (hzR : boxFinset z T ⊆ boxFinset u R) :
    (∫ η, matchedMeanH (clippedField η) ρ T x * matchedMeanH (clippedField η) ρ T z ∂(iidLaw d ν)) ≤
      Real.exp (holeSceneryConst d * ∑ y ∈ boxFinset u R,
        (1 - escapePotential d x y) * (1 - escapePotential d z y)) *
        ((∫ η, matchedMeanH (clippedField η) ρ T x ∂(iidLaw d ν)) *
          ∫ η, matchedMeanH (clippedField η) ρ T z ∂(iidLaw d ν)) := by
  have hd1 : 1 ≤ d := by omega
  have hm (y : Site d) : Measurable (fun η : Site d → ℤ => matchedMeanH (clippedField η) ρ T y) :=
    (measurable_matchedMeanH hd1 ρ T y).comp measurable_clippedField
  have hb (y : Site d) (η : Site d → ℤ) : |matchedMeanH (clippedField η) ρ T y| ≤ 1 := by
    rw [abs_of_nonneg (clippedMeanH_bounds hd1 η ρ T y).1]
    exact (clippedMeanH_bounds hd1 η ρ T y).2
  have hdep (y : Site d) (hy : boxFinset y T ⊆ boxFinset u R) (η ζ : Site d → ℤ)
      (he : ∀ v ∈ boxFinset u R, η v = ζ v) :
      matchedMeanH (clippedField η) ρ T y = matchedMeanH (clippedField ζ) ρ T y := by
    apply matchedMeanH_agree_box
    intro v hv
    exact congrArg clipSparse (he v (hy hv))
  have h := integral_product_factor (fun _ : Site d => ν)
    (fun η => matchedMeanH (clippedField η) ρ T x) (fun η => matchedMeanH (clippedField η) ρ T z)
    (hm x) (hm z) 1 1 (by norm_num) (hb x) (hb z) (sceneryHoleCost d x z)
    (fun S v hv η => scenery_hole_reveal_section hd ν ρ T x z hxz S v hv η)
    (boxFinset u R) (hdep x hxR) (hdep z hzR)
  have he : (∑ y ∈ boxFinset u R, sceneryHoleCost d x z y) =
      holeSceneryConst d * ∑ y ∈ boxFinset u R, (1 - escapePotential d x y) * (1 - escapePotential d z y) := by
    simp only [sceneryHoleCost, Finset.mul_sum, mul_assoc]
  rwa [he] at h
end Parking
