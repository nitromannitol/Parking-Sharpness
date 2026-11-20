import Parking.Support.OrientedBrownian
import Parking.Support.ValueBridge

/-!
# The one-dimensional Brownian stopping value

The coordinate map from the standard one-dimensional Brownian motion to the
quarter Brownian motion preserves stopping rules and bounded continuous
stopping payoffs.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace Parking

/-- A bounded continuous reward stopped at a natural stopping time is integrable. -/
theorem integrable_orientedBrownian_payoff {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsQuarterBrownian B P) {G : ℝ → ℝ → ℝ}
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) {M : ℝ}
    (hGM : ∀ s y, |G s y| ≤ M) {T : ℝ} (hT : 0 ≤ T)
    {τ : Ω → ℝ≥0} (hτ : IsNaturalStopping B τ) (hτT : ∀ ω, (τ ω : ℝ) ≤ T) :
    Integrable (fun ω => G (τ ω) (B (τ ω) ω)) P := by
  let W := orientedBrownianFamily B 0
  have hW : LatticeProb.IsBrownianSpace 1 0 W P := by
    have h := isBrownian_orientedBrownianFamily P B hB 0
    exact ⟨h.start, h.coord, h.indep⟩
  have hτW : IsNaturalStopping (ofBrownianSpace W) τ := by
    apply (Support.isBrownianStopping_add_iff W 0 τ).1
    simpa only [zero_add] using (isBrownianStopping_orientedBrownianFamily_iff B 0 τ).2 hτ
  let Z : ℝ → (Fin 1 → ℝ) → ℝ := fun s y => -G (T - s) (-(y 0) / 2)
  have hZc : Continuous (fun p : ℝ × (Fin 1 → ℝ) => Z p.1 p.2) := by
    have hmap : Continuous (fun p : ℝ × (Fin 1 → ℝ) => (T - p.1, -(p.2 0) / 2)) := by
      fun_prop
    exact (hG.comp hmap).neg
  have hZg : ∀ T', 0 < T' → ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T' ×ˢ (Set.univ : Set (Fin 1 → ℝ)),
        |Z p.1 p.2| ≤ C * (1 + ‖p.2‖) ^ k := by
    intro T' _
    refine ⟨M, 0, ?_⟩
    intro p _
    simpa [Z] using hGM (T - p.1) (-(p.2 0) / 2)
  have hi := Support.integrable_stoppingPayoff hW hZc hZg hT 0 hτW hτT
  simpa [Z, W, ofBrownianSpace, orientedBrownianFamily, sub_sub_cancel] using hi

/-- The DSP remaining-time discount is Parking's elapsed-time stopping value. -/
theorem brownianDiscount_orientedBrownianFamily_eq_contValue {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsQuarterBrownian B P)
    (G : ℝ → ℝ → ℝ) (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2))
    {M T : ℝ} (hGM : ∀ s y, |G s y| ≤ M) (hT : 0 ≤ T) :
    Sandpile.Continuum.brownianDiscount (orientedBrownianFamily B 0) P
      (fun s y => -G (T - s) (-(y 0) / 2)) T = contValue B P G T := by
  unfold Sandpile.Continuum.brownianDiscount contValue contPayoffs
  congr 1
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, rfl⟩
    have hτ' := (isBrownianStopping_orientedBrownianFamily_iff B 0 τ).1 hτ
    refine ⟨τ, hτ', hτT, integrable_orientedBrownian_payoff P B hB hG hGM hT hτ' hτT, ?_⟩
    simp [orientedBrownianFamily_zero_coord, sub_sub_cancel]
  · rintro ⟨τ, hτ, hτT, _, rfl⟩
    refine ⟨τ, (isBrownianStopping_orientedBrownianFamily_iff B 0 τ).2 hτ, hτT, ?_⟩
    simp [orientedBrownianFamily_zero_coord, sub_sub_cancel]

end Parking
