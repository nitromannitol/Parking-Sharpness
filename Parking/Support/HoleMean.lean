import Parking.Support.MatchedCountIntegral
import Parking.Support.MatchedBellman
import Parking.Support.FutureValue

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Expected remaining hole count with the initial field and priorities fixed. -/
def matchedMeanH (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) : ℝ :=
  ∫ σ, ((matchedState η ρ σ T).holes x : ℝ) ∂(roundNoiseLaw d)

theorem matchedMeanH_nonneg (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    0 ≤ matchedMeanH η ρ T x := integral_nonneg fun _ => Nat.cast_nonneg _

theorem matchedMeanH_le_initial (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (T : ℕ) (x : Site d) : matchedMeanH η ρ T x ≤ ((-η x).toNat : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  have h := integral_mono (integrable_matchedHoles hd η ρ T x (roundNoiseLaw d))
    (integrable_const ((-η x).toNat : ℝ)) (fun σ => Nat.cast_le.mpr (matchedHoles_le_initial η ρ σ T x))
  simpa only [matchedMeanH, integral_const, probReal_univ, one_smul] using h

theorem matchedMeanH_zero (hd : 1 ≤ d) (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ) (x : Site d) :
    matchedMeanH η ρ 0 x = ((-η x).toNat : ℝ) := by
  haveI := roundNoiseLaw_isProbability hd
  simp [matchedMeanH, matchedState, initial]

theorem measurable_matchedMeanH (hd : 1 ≤ d) (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    Measurable (fun η : Site d → ℤ => matchedMeanH η ρ T x) := by
  haveI := roundNoiseLaw_isProbability hd
  have hS := measurableState_matchedState ⟨0, hd⟩
    (Ω := (Site d → ℤ) × RoundNoise d) Prod.fst (fun _ => ρ) Prod.snd
    measurable_fst measurable_const measurable_snd T
  exact ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp
    (hS.2.2.1 x)).stronglyMeasurable.integral_prod_right'.measurable

/-- Removing the first round leaves precisely the restarted hole process. -/
theorem matchedHoles_cons (η : Site d → ℤ) (ρ : Label d × ℕ → ℝ)
    (τ : RoundSlot d → Fin d × Bool) (σ : RoundNoise d) (T : ℕ) (x : Site d) :
    (matchedState η ρ (consNat τ σ) (T + 1)).holes x =
      (matchedState (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ σ T).holes x := by
  have h := (matchedState_restart η ρ ρ (consNat τ σ) 1 T).2.1 x
  rw [Nat.add_comm 1 T, matchedRestart_one] at h
  have he : (fun n => consNat τ σ (1 + n)) = σ := by
    funext n
    rw [Nat.add_comm, consNat_succ]
  rwa [he] at h

/-- Expected remaining holes obey the first-round averaging identity. -/
theorem matchedMeanH_bellman (hd : 1 ≤ d) (η : Site d → ℤ)
    (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) :
    matchedMeanH η ρ (T + 1) x =
      ∫ τ, matchedMeanH (roundSigned (fun y => (η y).toNat) (fun y => (-η y).toNat) τ) ρ T x
        ∂(Measure.infinitePi fun _ : RoundSlot d => stepLaw d) := by
  haveI := stepLaw_isProbability hd
  haveI := roundNoiseLaw_isProbability hd
  let Q := Measure.infinitePi fun _ : RoundSlot d => stepLaw d
  have hfi := integrable_matchedHoles hd η ρ (T + 1) x (roundNoiseLaw d)
  change (∫ σ, ((matchedState η ρ σ (T + 1)).holes x : ℝ) ∂(roundNoiseLaw d)) = _
  have he : (∫ σ, ((matchedState η ρ σ (T + 1)).holes x : ℝ) ∂(roundNoiseLaw d)) =
      ∫ τ, ∫ σ, ((matchedState η ρ (consNat τ σ) (T + 1)).holes x : ℝ) ∂(roundNoiseLaw d) ∂Q :=
    integral_infinitePi_nat_head_tail Q _ hfi
  rw [he]
  simp only [matchedHoles_cons, matchedMeanH]
  rfl
end Parking
