/-
Proposition 11.4 of parking.tex, frozen.  `parking.tex:2829-2845` (label
`prop:near-divisible`), in the setting of `parking.tex:2573-2583`:

  "For all sufficiently small $\delta>0$,
   $\E u_\infty^\delta(0)\leq C\delta^{-3}$ for $d=1$, $C\delta^{-1}$ for
   $d=2$, $C\delta^{-1/3}$ for $d=3$, $C\log(e/\delta)$ for $d\geq4$.
   The reverse inequality holds when $d\leq4$, and when $d\geq5$ the lower
   bound is $c[\log(e/\delta)]^{2/d}$.  If in addition $\eta_\delta(0)$ is
   bounded uniformly in $\delta$, then
   $\E u_\infty^\delta(0)\asymp[\log(e/\delta)]^{2/d}$ when $d\geq5$."

The four upper rates are `Parking.nearRate`, the function already used by
`thm:near`.  The mean is read in `ℝ≥0∞` as the supremum of the increasing
sequence `E u_n^δ(0)`, so that an infinite mean is `⊤` and not a junk value.
"Bounded uniformly in `δ`" is a common bound on the support of every `ν δ`.
The results the proof quotes without proving them here enter as explicit
hypotheses.  Step 1 applies `lem:mean-horizon`, whose own Step 1 cites
`eq:green-norms` at `parking.tex:2790`, and Step 3 reads the two Green rates
again at a bounded reference law, so standing ruling R1 attaches
`Parking.External.GreenNorms` as a fourth explicit hypothesis.
-/
import Parking.Support.NearBounded
import Parking.External.SandpileGrowth
import Parking.External.Stopping
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.Support.Near

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.near_divisible (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (hConcentration : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms) (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (ν : ℝ → Measure ℤ)
    (θ M K : ℝ) (hfam : Parking.NearFamily δ₀ ν θ M K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁,
        Parking.meanuLimit (Parking.law d (ν δ))
            ≤ ENNReal.ofReal (C * Parking.nearRate d δ) ∧
          (d ≤ 4 → ENNReal.ofReal (c * Parking.nearRate d δ)
            ≤ Parking.meanuLimit (Parking.law d (ν δ))) ∧
          (5 ≤ d → ENNReal.ofReal (c * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d))
            ≤ Parking.meanuLimit (Parking.law d (ν δ))) ∧
          (5 ≤ d → (∃ B : ℤ, ∀ δ' ∈ Set.Icc (0 : ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0) →
            ENNReal.ofReal (c * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d))
                ≤ Parking.meanuLimit (Parking.law d (ν δ)) ∧
              Parking.meanuLimit (Parking.law d (ν δ))
                ≤ ENNReal.ofReal (C * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d)))
-- FROZEN-STATEMENT-END
:= by
  classical
  obtain ⟨hδ₀, hθ, hprob, hmeanν, hnc, hexpm, hcoup⟩ := id hfam
  have hrateNonneg : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ Parking.nearRate d δ := by
    intro δ hδ0 hδ1
    have hlog : (0:ℝ) ≤ Real.log (Real.exp 1 / δ) := by
      refine Real.log_nonneg ?_
      rw [le_div_iff₀ hδ0]
      nlinarith [Real.one_le_exp (le_refl (0:ℝ)), Real.add_one_le_exp (1:ℝ)]
    rw [Parking.nearRate]
    split_ifs
    · positivity
    · positivity
    · positivity
    · exact hlog
  have hpsiNonneg : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (0:ℝ) ≤ Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d) := by
    intro δ hδ0 hδ1
    exact Real.rpow_nonneg (Real.log_nonneg (by
      rw [le_div_iff₀ hδ0]
      nlinarith [Real.add_one_le_exp (1:ℝ), hδ0])) _
  obtain ⟨CU, hCU, hupper⟩ :=
    Parking.exists_meanuLimit_upper (d := d) hd hGrowth hStopping hConcentration hGreen hfam
  obtain ⟨cL, δL, hcL, hδL, hδL0, hlower⟩ :=
    Parking.exists_meanuLimit_lower (d := d) hd hGrowth hfam
  by_cases hcase : 5 ≤ d ∧ ∃ B : ℤ, ∀ δ' ∈ Set.Icc (0:ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0
  · obtain ⟨hd5, B, hB⟩ := hcase
    obtain ⟨CP, δP, hCP, hδP, hδP0, hpsi⟩ :=
      Parking.exists_meanuLimit_psi_upper (d := d) hd5 hGrowth hStopping hConcentration hGreen
        hfam hB
    refine ⟨cL, max CU CP, hcL, lt_of_lt_of_le hCU (le_max_left _ _),
      min 1 (min δL δP), lt_min one_pos (lt_min hδL hδP),
      le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hδL0), fun δ hδ => ?_⟩
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ ≤ 1 := le_trans hδ.2 (min_le_left _ _)
    have hδLle : δ ≤ δL := le_trans hδ.2 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδPle : δ ≤ δP := le_trans hδ.2 (le_trans (min_le_right _ _) (min_le_right _ _))
    have hδ₀le : δ ≤ δ₀ := le_trans hδLle hδL0
    have hlowδ := hlower δ ⟨hδ0, hδLle⟩
    have hupδ := hupper δ ⟨hδ0.le, hδ₀le⟩ hδ0 hδ1
    have hpsiδ := hpsi δ ⟨hδ0, hδPle⟩
    have hup : Parking.meanuLimit (Parking.law d (ν δ))
        ≤ ENNReal.ofReal (max CU CP * Parking.nearRate d δ) := by
      refine le_trans hupδ (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hrateNonneg δ hδ0 hδ1)
    have hlow5 : ENNReal.ofReal (cL * Real.log (Real.exp 1 / δ) ^ ((2 : ℝ) / d))
        ≤ Parking.meanuLimit (Parking.law d (ν δ)) := by
      rw [Parking.nearLowerTarget, if_neg (by omega : ¬ d ≤ 4)] at hlowδ
      exact hlowδ
    refine ⟨hup, fun h4 => absurd h4 (by omega), fun _ => hlow5, fun _ _ => ⟨hlow5, ?_⟩⟩
    refine le_trans hpsiδ (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hpsiNonneg δ hδ0 hδ1)
  · refine ⟨cL, CU, hcL, hCU, min 1 δL, lt_min one_pos hδL,
      le_trans (min_le_right _ _) hδL0, fun δ hδ => ?_⟩
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ ≤ 1 := le_trans hδ.2 (min_le_left _ _)
    have hδLle : δ ≤ δL := le_trans hδ.2 (min_le_right _ _)
    have hδ₀le : δ ≤ δ₀ := le_trans hδLle hδL0
    have hlowδ := hlower δ ⟨hδ0, hδLle⟩
    have hupδ := hupper δ ⟨hδ0.le, hδ₀le⟩ hδ0 hδ1
    refine ⟨hupδ, fun h4 => ?_, fun h5 => ?_, fun h5 hbdd => absurd ⟨h5, hbdd⟩ hcase⟩
    · rw [Parking.nearLowerTarget, if_pos h4] at hlowδ
      exact hlowδ
    · rw [Parking.nearLowerTarget, if_neg (by omega : ¬ d ≤ 4)] at hlowδ
      exact hlowδ
