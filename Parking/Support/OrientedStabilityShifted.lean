import Parking.Support.OrientedStoppingProjection
import Parking.Support.OrientedBrownianValue
import Sandpile.External.ContStoppingStability
import Sandpile.Support.MainExplWalkValue

/-!
# Stability for the shifted oriented reward

The one-dimensional sandpile stability input gives convergence for the elapsed
reward shifted by the difference between the continuum horizon and its discrete
floor. This shift is nonnegative and tends to zero.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The difference between the continuum and discrete horizons. -/
def orientedHorizonShift (n : ℕ) (T : ℝ) : ℝ :=
  T - (⌊(n : ℝ) * T⌋₊ : ℝ) / n

/-- DSP stability implies stability for the reward evaluated at the shifted
    elapsed time. -/
theorem orientedStoppingSup_shifted_of_continuumStoppingStability
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsQuarterBrownian B P)
    {T M : ℝ} (hT : 0 < T) (_hM : 0 ≤ M)
    (G : ℝ → ℝ → ℝ) (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    (hGM : ∀ s y, |G s y| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |orientedStoppingSup 2
        (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (orientedScaledSite n z))
        ⌊(n : ℝ) * T⌋₊ 0 - contValue B P G T| ≤ ε := by
  let H : ℝ → Sandpile.Continuum.Space 1 → ℝ := fun s y => G (T - s) (-(y 0) / 2)
  have hH : Continuous (fun p : ℝ × Sandpile.Continuum.Space 1 => H p.1 p.2) := by
    have hm : Continuous (fun p : ℝ × Sandpile.Continuum.Space 1 =>
        (T - p.1, -(p.2 0) / 2)) := by fun_prop
    exact hG.comp hm
  intro ε hε
  obtain ⟨R₀, hR₀, hstab⟩ := hStab 1 (by norm_num) Ω P (orientedBrownianFamily B)
    (isBrownian_orientedBrownianFamily P B hB) T T hT le_rfl {0} isCompact_singleton
    H hH (fun _ => H) M (fun s y => hGM _ _) (fun R s y => hGM _ _)
    (by intro δ hδ; exact ⟨1, zero_lt_one, fun R hR s hs y => by simp [hδ.le]⟩) ε hε
  have hlarge : ∀ᶠ n : ℕ in atTop, R₀ ≤ Real.sqrt n :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop R₀
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnc : (0 : ℝ) < n := by exact_mod_cast hn0
  have hroot : (Real.sqrt (n : ℝ)) ^ 2 = n := Real.sq_sqrt hnc.le
  have hs := hstab (Real.sqrt n) (hN n (by omega)) T ⟨le_rfl, le_rfl⟩ 0 (by simp)
  have hx : (fun i : Fin 1 => ⌊Real.sqrt (n : ℝ) * (0 : Sandpile.Continuum.Space 1) i⌋) = 0 := by
    ext i
    simp
  rw [hroot, hx, brownianDiscount_orientedBrownianFamily_eq_contValue P B hB G hG hGM hT.le] at hs
  have heq : orientedStoppingSup 2
      (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (orientedScaledSite n z))
      ⌊(n : ℝ) * T⌋₊ 0 =
      Sandpile.stoppingSup ⌊(n : ℝ) * T⌋₊ 0
        (fun k X => H (((⌊(n : ℝ) * T⌋₊ : ℕ) - (k : ℝ)) / n)
          (Sandpile.External.Lclt.scaledSite (Real.sqrt n) (X k))) := by
    let F : ℕ → Sandpile.Site 1 → ℝ := fun k z =>
      G ((k : ℝ) / n + orientedHorizonShift n T) (-((z 0 : ℤ) : ℝ) / (2 * Real.sqrt n))
    have heqF : (fun (k : ℕ) (z : Site 2) => G ((k : ℝ) / n + orientedHorizonShift n T)
        (orientedScaledSite n z)) = (fun k z => F k (orientedProjectSite z)) := by
      funext k z
      congr 1
      simp only [orientedProjectSite, orientedScaledSite, Int.cast_sub]
      ring
    rw [heqF, orientedStoppingSup_eq_sandpile_stoppingSup]
    apply Sandpile.stoppingSup_congr_of_le
    intro k hk X
    dsimp [F, H, orientedHorizonShift, Sandpile.External.Lclt.scaledSite]
    congr 1 <;> ring
  rw [← heq] at hs
  exact hs

end Parking
