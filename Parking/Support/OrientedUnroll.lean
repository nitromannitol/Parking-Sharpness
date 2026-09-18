/- The directed error at the origin, unrolled as the sum over the rounds of the
finite route sums (`parking.tex:3240-3250`). -/
import Parking.Support.OrientedSiteRound
import Parking.Support.OrientedFiniteRoute

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Finset
variable {d : ℕ}

/-- The directed error at the origin is the sum over the rounds `k < n` of the
finite route sum of that round, with the departure stacks truncated at the box
of radius `n + 1`. -/
theorem wErrOriented_eq_sum_finiteRoute (η : Site d → ℤ) (σ : Site d × ℕ → Site d)
    (hσ : ∀ q : Site d × ℕ, ∃ i : Fin d, σ q = q.1 + unit i) (n : ℕ) :
    wErrOriented η σ n 0 = ∑ k ∈ Finset.range n,
      orientedFiniteRoute (boxFinset (0 : Site d) (n + 1)) (fun _ => k) (fun _ => n - (k + 1))
        (η, σ) := by
  rw [wErrOriented_eq_siteRoundSum η σ hσ n]
  simp only [orientedFiniteRoute]
  rw [Finset.sum_comm]

end Parking
end
