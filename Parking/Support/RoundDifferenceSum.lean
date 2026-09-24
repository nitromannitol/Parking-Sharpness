import Parking.Support.RoundDifference
import Parking.Support.RoundBlock
import Parking.Support.ProductSetCongr

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d K : ℕ}

/-- A complete finite round reveal sums to the realized future mean minus its average. -/
theorem sum_roundDiff (hd : 1 ≤ d) (e : Fin K ↪ Site d × ℕ)
    (A H : Site d → ℕ) (N : ℕ) (hA : ∀ y, A y ≤ N)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d)
    (hcover : ∀ y ∈ boxFinset x (T + 1), ∀ j < N, ∃ i, e i = (y, j))
    (τ : RoundSlot d → Fin d × Bool) :
    ∑ j : Fin K, roundDiff e A H ρ T x j τ = matchedMeanU (roundSigned A H τ) ρ T x -
      ∫ ζ, matchedMeanU (roundSigned A H ζ) ρ T x
        ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  classical
  haveI := stepLaw_isProbability hd
  let P : ℕ → ℝ := fun n => partialInt (fun _ : RoundSlot d => stepLaw d)
    (revealPrefix (slotEnumeration e) n) (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ
  have hsum : (∑ j : Fin K, roundDiff e A H ρ T x j τ) = P K - P 0 := by
    change (∑ j : Fin K, (P (j.val + 1) - P j.val)) = _
    exact (Fin.sum_univ_eq_sum_range (fun n => P (n + 1) - P n) K).trans (Finset.sum_range_sub P K)
  have hlast : P K = matchedMeanU (roundSigned A H τ) ρ T x := by
    dsimp only [P]
    apply partialInt_eq_self
    intro ζ ζ' he
    apply roundMeanU_agree_finite A H N hA ρ T x ζ ζ'
    intro y hy j hj
    obtain ⟨i, hi⟩ := hcover y hy j hj
    apply he (Sum.inl (y, j))
    exact ⟨i, i.isLt, congrArg Sum.inl hi⟩
  have hfirst : P 0 = ∫ ζ, matchedMeanU (roundSigned A H ζ) ρ T x
      ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
    dsimp only [P]
    exact (partialInt_set_congr _ _ ∅ (revealPrefix_zero (slotEnumeration e)) _ τ).trans rfl
  rw [hsum, hlast, hfirst]
end Parking
