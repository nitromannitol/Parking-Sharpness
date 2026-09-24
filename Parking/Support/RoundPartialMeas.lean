import Parking.Support.RoundMeanField
import Parking.Support.ProductTower

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Partial current-round future means vary measurably with the revealed past and current table. -/
theorem measurable_partialRoundMean {Ω : Type*} [MeasurableSpace Ω]
    (hd : 1 ≤ d) (A H : Ω → Site d → ℕ) (τ : Ω → RoundSlot d → Fin d × Bool)
    (hA : Measurable A) (hH : Measurable H) (hτ : Measurable τ)
    (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)] (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    Measurable (fun ω => partialInt (fun _ : RoundSlot d => stepLaw d) S
      (fun ζ => matchedMeanU (roundSigned (A ω) (H ω) ζ) ρ T x) (τ ω)) := by
  haveI := stepLaw_isProbability hd
  have hm : Measurable (fun p : Ω × (RoundSlot d → Fin d × Bool) => comb S (τ p.1) p.2) :=
    (measurable_comb S).comp ((hτ.comp measurable_fst).prodMk measurable_snd)
  have hf : Measurable (fun p : Ω × (RoundSlot d → Fin d × Bool) =>
      matchedMeanU (roundSigned (A p.1) (H p.1) (comb S (τ p.1) p.2)) ρ T x) :=
    (measurable_matchedMeanU hd ρ T x).comp (measurable_roundSigned _ _ _
      (hA.comp measurable_fst) (hH.comp measurable_fst) hm)
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

/-- A bounded outgoing count gives a uniform bound on every partial current-round future mean. -/
theorem partialRoundMean_bound (hd : 1 ≤ d) (A H : Site d → ℕ)
    (N : ℕ) (hA : ∀ y, A y ≤ N) (S : Set (RoundSlot d)) [DecidablePred (· ∈ S)]
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (τ : RoundSlot d → Fin d × Bool) :
    |partialInt (fun _ : RoundSlot d => stepLaw d) S
      (fun ζ => matchedMeanU (roundSigned A H ζ) ρ T x) τ| ≤
        ((T * ((2 * T + 1) ^ d * (2 * d * N)) : ℕ) : ℝ) := by
  haveI := stepLaw_isProbability hd
  exact abs_partialInt_le _ _ _ _ (roundMeanU_bound hd A H N hA ρ T x) τ
end Parking
