import Parking.Support.MatchedMeanBalance
import Parking.Support.MatchedMonotone

/-!
# Monotonicity of the mean odometer's Laplacian

If two initial fields `η ≤ ζ` agree at a site `x` and are bounded by a common constant `K`,
the mean odometer's discrete Laplacian `walkOp (matchedMeanU · ρ t) x - matchedMeanU · ρ t x`
at `x` is monotone in the field, comparing `η` against `ζ`. The proof rewrites both sides via
the signed balance identity `matchedMeanU_signed_balance` and compares the resulting
particle- and hole-count integrals termwise using `matched_counts_mono`.
-/

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Ordered initial fields give ordered mean Laplacians wherever the initial values agree. -/
theorem matchedMeanU_laplacian_mono (hd : 1 ≤ d) (η ζ : Site d → ℤ) (hηζ : ∀ y, η y ≤ ζ y)
    (K : ℕ) (hζ : ∀ y, (ζ y).toNat ≤ K) (ρ : Label d × ℕ → ℝ) (t : ℕ) (x : Site d)
    (hx : η x = ζ x) :
    walkOp (matchedMeanU η ρ t) x - matchedMeanU η ρ t x ≤
      walkOp (matchedMeanU ζ ρ t) x - matchedMeanU ζ ρ t x := by
  haveI := roundNoiseLaw_isProbability hd
  have hη (y : Site d) : (η y).toNat ≤ K := (Int.toNat_le_toNat (hηζ y)).trans (hζ y)
  rw [matchedMeanU_signed_balance hd η K hη ρ t x, matchedMeanU_signed_balance hd ζ K hζ ρ t x, hx]
  have hA := integral_mono (integrable_matchedCount_bounded hd η K hη ρ t x (roundNoiseLaw d))
    (integrable_matchedCount_bounded hd ζ K hζ ρ t x (roundNoiseLaw d))
    (fun σ => Nat.cast_le.mpr ((matched_counts_mono η ζ hηζ ρ ρ σ t).1 x))
  have hH := integral_mono (integrable_matchedHoles hd ζ ρ t x (roundNoiseLaw d))
    (integrable_matchedHoles hd η ρ t x (roundNoiseLaw d))
    (fun σ => Nat.cast_le.mpr ((matched_counts_mono η ζ hηζ ρ ρ σ t).2.1 x))
  linarith
end Parking
