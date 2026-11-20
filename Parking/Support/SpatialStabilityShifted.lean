import Parking.Support.SpatialWalkProjection
import Parking.Support.ValueBridge
import Parking.Support.OrientedStabilityShifted
import Sandpile.External.ContStoppingStability

/-!
# Stability for the shifted spatial reward

The Brownian value of the translated motion with the remaining-time reward is the spatial
elapsed-time value.  The continuum stopping stability of the divisible sandpile then gives
convergence of the simple random walk stopping values for the reward read at the elapsed time
shifted by the difference between the continuum horizon and its discrete floor.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- The sandpile remaining-time discount of the motion is the spatial elapsed-time value. -/
theorem brownianDiscount_eq_spatialContValue {ΩB : Type} [MeasurableSpace ΩB]
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {d : ℕ}
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    (G : ℝ → (Fin d → ℝ) → ℝ) (hG : Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2))
    {M T : ℝ} (hGM : ∀ s y, |G s y| ≤ M) (hT : 0 ≤ T) :
    Sandpile.Continuum.brownianDiscount
        (fun s β => (0 : Sandpile.Continuum.Space d) + B s β) PB
        (fun s y => -G (T - s) (WithLp.ofLp y)) T =
      spatialContValue (ofBrownianSpace B) PB G T := by
  let Z : ℝ → (Fin d → ℝ) → ℝ := fun s y => -G (T - s) y
  have hZc : Continuous (fun p : ℝ × (Fin d → ℝ) => Z p.1 p.2) := by
    have hm : Continuous (fun p : ℝ × (Fin d → ℝ) => (T - p.1, p.2)) := by fun_prop
    exact (hG.comp hm).neg
  have hZg : ∀ T', 0 < T' → ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T' ×ˢ (Set.univ : Set (Fin d → ℝ)),
        |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k := by
    intro T' _
    refine ⟨M, 0, fun p _ => ?_⟩
    simpa [Z] using hGM (T - p.1) p.2
  have hpt : ∀ (τ : ΩB → ℝ≥0) (β : ΩB),
      -(-G (T - (T - (τ β : ℝ))) (WithLp.ofLp ((0 : Sandpile.Continuum.Space d) + B (τ β) β))) =
        G (τ β) (ofBrownianSpace B (τ β) β) := by
    intro τ β
    rw [neg_neg, sub_sub_cancel, zero_add]
    rfl
  unfold Sandpile.Continuum.brownianDiscount spatialContValue spatialContPayoffs
  congr 1
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, rfl⟩
    have hτ' := (Support.isBrownianStopping_add_iff B 0 τ).1 hτ
    have hi := Support.integrable_stoppingPayoff hB hZc hZg hT 0 hτ' hτT
    refine ⟨τ, hτ', hτT, by simpa [Z] using hi, ?_⟩
    exact integral_congr_ae (Filter.Eventually.of_forall fun β => hpt τ β)
  · rintro ⟨τ, hτ, hτT, _, rfl⟩
    refine ⟨τ, (Support.isBrownianStopping_add_iff B 0 τ).2 hτ, hτT, ?_⟩
    exact (integral_congr_ae (Filter.Eventually.of_forall fun β => hpt τ β)).symm

/-- **Continuum stopping stability gives convergence for the shifted spatial reward.** -/
theorem stoppingSup_shifted_of_continuumStoppingStability
    (hStab : Sandpile.External.ContinuumStoppingStability.{0}) {d : ℕ} (hd : 1 ≤ d)
    (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (B : ℝ≥0 → ΩB → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B PB)
    {T M : ℝ} (hT : 0 < T)
    (G : ℝ → (Fin d → ℝ) → ℝ) (hG : Continuous (fun p : ℝ × (Fin d → ℝ) => G p.1 p.2))
    (hGM : ∀ s y, |G s y| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |stoppingSup d
        (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (spatialScaledSite n z))
        ⌊(n : ℝ) * T⌋₊ 0 - spatialContValue (ofBrownianSpace B) PB G T| ≤ ε := by
  let H : ℝ → Sandpile.Continuum.Space d → ℝ := fun s y => G (T - s) (WithLp.ofLp y)
  have hH : Continuous (fun p : ℝ × Sandpile.Continuum.Space d => H p.1 p.2) := by
    have hm : Continuous (fun p : ℝ × Sandpile.Continuum.Space d =>
        (T - p.1, WithLp.ofLp p.2)) := by fun_prop
    exact hG.comp hm
  intro ε hε
  obtain ⟨R₀, hR₀, hstab⟩ := hStab d hd ΩB PB (fun x s β => x + B s β)
    (fun x => Support.isBrownian_add_of_isBrownianSpace hB x) T T hT le_rfl {0}
    isCompact_singleton H hH (fun _ => H) M (fun s y => hGM _ _) (fun R s y => hGM _ _)
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
  have hx : (fun i : Fin d => ⌊Real.sqrt (n : ℝ) * (0 : Sandpile.Continuum.Space d) i⌋) = 0 := by
    ext i
    simp
  rw [hroot, hx, brownianDiscount_eq_spatialContValue PB B hB G hG hGM hT.le] at hs
  have heq : stoppingSup d
      (fun k z => G ((k : ℝ) / n + orientedHorizonShift n T) (spatialScaledSite n z))
      ⌊(n : ℝ) * T⌋₊ 0 =
      Sandpile.stoppingSup ⌊(n : ℝ) * T⌋₊ 0
        (fun k X => H (((⌊(n : ℝ) * T⌋₊ : ℕ) - (k : ℝ)) / n)
          (Sandpile.External.Lclt.scaledSite (Real.sqrt n) (X k))) := by
    rw [stoppingSup_eq_sandpile_stoppingSup hd]
    apply Sandpile.stoppingSup_congr_of_le
    intro k _ X
    dsimp only [H, orientedHorizonShift, Sandpile.External.Lclt.scaledSite]
    congr 1
    ring
  rw [← heq] at hs
  exact hs

end Parking
