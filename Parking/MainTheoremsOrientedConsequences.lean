import Parking.MainTheoremsBernsteinConsequences
import Parking.External.OrientedStoppingStabilityOfDSP

/-!
# Oriented results from continuum stopping stability

The continuum stopping stability of the divisible sandpile supplies the
oriented stopping input for the oriented scaling and walk results.
-/

open MeasureTheory Filter Topology

/-- The oriented scaling limit with continuum stopping stability supplied. -/
theorem Parking.oriented_scaling_of_continuum_stopping
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Q : Measure Ω) (_ : IsProbabilityMeasure Q)
      (Uc : ℝ → Ω → ℝ) (μ : ℝ),
      (∀ T : ℝ, 0 < T → Measurable (Uc T)) ∧
      (∀ T : ℝ, 0 < T → ∀ F : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun n : ℕ => ∫ w, F ((n : ℝ) ^ (-(1 : ℝ) / 4) *
              Parking.uOriented (fun y => (w.1 y : ℝ)) ⌊(n : ℝ) * T⌋₊ 0)
            ∂(Parking.orientedLaw 2 ν)) atTop (𝓝 (∫ ω, F (Uc T ω) ∂Q))) ∧
      (∀ T : ℝ, 0 < T → Q.map (Uc T) = Q.map fun ω => T ^ ((1 : ℝ) / 4) * Uc 1 ω) ∧
      Integrable (Uc 1) Q ∧ μ = ∫ ω, Uc 1 ω ∂Q ∧ 0 < μ ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ) / 4) *
        Parking.meanuOriented (Parking.orientedLaw 2 ν) n) atTop (𝓝 μ) :=
  Parking.Frozen.oriented_scaling
    (Parking.External.orientedStoppingStability_of_continuumStoppingStability hStab) ν hν

/-- The oriented walk theorem with continuum stopping stability supplied. -/
theorem Parking.oriented_walk_of_continuum_stopping (hBern : Parking.External.Bernstein)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
        Parking.meanuOriented (Parking.orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => Parking.S (Parking.orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) :=
  Parking.oriented_walk hBern
    (Parking.External.orientedStoppingStability_of_continuumStoppingStability hStab) d hd ν hν

/-- The oriented walk theorem with Bernstein and continuum stopping stability supplied. -/
theorem Parking.oriented_walk_of_bernstein_and_continuum_stopping (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (d : ℕ) (hd : 2 ≤ d) (ν : Measure ℤ)
    (hν : Parking.CriticalLaw ν) :
    (d = 2 → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4)) ∧
    (3 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * Real.log n ≤ Parking.meanU (Parking.orientedLaw d ν) n ∧
        Parking.meanU (Parking.orientedLaw d ν) n ≤ C * Real.log n) ∧
    (d = 2 →
      Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
        Parking.meanuOriented (Parking.orientedLaw d ν) n) atTop (𝓝 1) ∧
      ∃ μ : ℝ, 0 < μ ∧
        Tendsto (fun n : ℕ => Parking.meanU (Parking.orientedLaw d ν) n /
          (μ * (n : ℝ) ^ ((1 : ℝ) / 4))) atTop (𝓝 1) ∧
        Tendsto (fun t : ℕ => Parking.S (Parking.orientedLaw d ν) t /
          (μ / 4 * (t : ℝ) ^ (-(3 : ℝ) / 4))) atTop (𝓝 1)) :=
  Parking.oriented_walk_of_bernstein
    (Parking.External.orientedStoppingStability_of_continuumStoppingStability hStab) d hd ν hν
