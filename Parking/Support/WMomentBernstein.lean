import Parking.External.BernsteinProved
import Parking.Support.WMomentProof

/-!
# Moment bounds for the error

The moment bounds hold with the martingale Bernstein input supplied.
-/

open MeasureTheory

namespace Parking

variable {d : ℕ}

/-- A moment constant uniform over all admissible laws. -/
theorem exists_wErr_moment_const_uniform_of_bernstein (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (⨆ m ∈ Set.Iic n, (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * kappa d n *
            (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)) + r) :=
  exists_wErr_moment_const_uniform hd Parking.External.bernstein

/-- A moment constant for a single admissible law. -/
theorem exists_wErr_moment_const_of_bernstein (hd : 1 ≤ d)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (⨆ m ∈ Set.Iic n, (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * kappa d n *
            (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)) + r) :=
  exists_wErr_moment_const hd Parking.External.bernstein ν hθ hexp

end Parking
