import Parking.External.BernsteinProved
import Parking.Support.TableBernstein

/-!
# A moment bound for the table martingale

The table noise moment bound holds using the martingale Bernstein estimates.
-/

open MeasureTheory
open LatticeProb.MomentNorm (rNorm)

/-- The table noise moment bound with the Bernstein input supplied. -/
theorem Parking.exists_table_noise_moment_bound_of_bernstein :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 3 ≤ d → ∀ (η : Parking.Site d → ℤ),
      (∀ y, (η y).toNat ≤ 1) → ∀ (ρ : Parking.Label d × ℕ → ℝ) (T : ℕ)
      (x : Parking.Site d) (r : ℝ), 2 ≤ r →
      rNorm (Parking.flatRoundNoiseLaw d) r (fun ω =>
        ((Parking.matchedState η ρ (Parking.curryRoundNoise ω) T).departures x : ℝ) -
          Parking.matchedMeanU η ρ T x) ≤
        C * (Real.sqrt r * (∫ ω, Parking.greenWeightedOdometer η ρ
          (Parking.curryRoundNoise ω) T x T ^ (r / 2)
          ∂(Parking.flatRoundNoiseLaw d)) ^ (1 / r) + r * Parking.escapeConst d) :=
  Parking.exists_table_noise_moment_bound Parking.External.bernstein
