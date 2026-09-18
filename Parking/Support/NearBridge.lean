/-
The moment of the particle-law odometer against the moment of the recentred odometer
(`parking.tex:2952-2955`).

"Since `η_δ ≤ ξ_δ`, monotonicity and `eq:near-centered-moment` bound
`(E u_n^δ(0)^r)^{1/r}`."

The odometer of the configuration is the odometer of the recentred scenery at `δ = 0`,
and the sandpile odometer is monotone in the scenery, so raising `δ` from `0` raises the
odometer at every realization and hence every moment of it.  Both moments are finite
because the odometer at a finite horizon reads only the coordinates of a finite box and
is Lipschitz in them, and the one-site law has an exponential moment.
-/
import Parking.Support.NearEnv
import Parking.Support.NearMoment
import Parking.Support.UConcBridge
import Parking.Support.NearLower
import Parking.Support.UConcReal
import Parking.Support.XiLaw

open MeasureTheory LatticeProb

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The odometer of the configuration is the odometer of the recentred scenery at
`δ = 0`. -/
theorem uOf_eq_u_xi_zero (ω : Data d) (n : ℕ) (x : Site d) :
    Parking.uOf ω n x = u (Parking.xi 0 ω.1) n x := by
  refine congrArg (fun f => u f n x) ?_
  funext y
  simp [Parking.xi]

/-- **The moment of the odometer against the moment of the recentred odometer.**
Since `η_δ ≤ ξ_δ` for `δ ≥ 0`, monotonicity in the scenery raises the moment. -/
theorem integral_uOf_rpow_le_xi (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexpabs : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν)
    {δ : ℝ} (hδ : 0 ≤ δ) {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    ∫ ω, |Parking.uOf ω n 0| ^ r ∂(Parking.law d ν)
      ≤ ∫ η, |u (Parking.xi δ η) n 0| ^ r ∂(LatticeProb.iidLaw d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  have hG : Measurable (fun ζ : Site d → ℝ => |u ζ n 0| ^ r) :=
    (measurable_u_eval n 0).abs.pow_const r
  have hxim : ∀ e : ℝ, Measurable (fun η : Site d → ℤ => Parking.xi e η) := fun e =>
    measurable_pi_lambda _ fun y =>
      (measurable_intCastReal.comp (measurable_pi_apply y)).add_const e
  have hmap : ∀ e : ℝ, ∫ ζ, |u ζ n 0| ^ r ∂(LatticeProb.iidLaw d (shiftLaw e ν))
      = ∫ η, |u (Parking.xi e η) n 0| ^ r ∂(LatticeProb.iidLaw d ν) := by
    intro e
    rw [← law_map_xi (d := d) e ν]
    exact integral_map (hxim e).aemeasurable hG.aestronglyMeasurable
  have hLHS : ∫ ω, |Parking.uOf ω n 0| ^ r ∂(Parking.law d ν)
      = ∫ ζ, |u ζ n 0| ^ r ∂(LatticeProb.iidLaw d (shiftLaw 0 ν)) := by
    rw [shiftLaw_zero, realLaw]
    exact integral_confReal hd ν hG
  have hInt : ∀ e : ℝ, Integrable (fun η : Site d → ℤ => |u (Parking.xi e η) n 0| ^ r)
      (LatticeProb.iidLaw d ν) := by
    intro e
    haveI : IsProbabilityMeasure (shiftLaw e ν) := by
      rw [shiftLaw]
      exact Measure.isProbabilityMeasure_map (measurable_intShift e).aemeasurable
    have hexpe : Integrable (fun z : ℝ => Real.exp (θ * |z|)) (shiftLaw e ν) :=
      integrable_exp_abs_shiftLaw θ e hθ.le ν hexpabs
    have hpow : Integrable (fun t : ℝ => max t 0 ^ (⌈r⌉₊)) (shiftLaw e ν) :=
      integrable_maxPow_of_exp (shiftLaw e ν) hθ hexpe _
    have hbase : Integrable (fun ζ : Site d → ℝ => |u ζ n 0| ^ r)
        (LatticeProb.iidLaw d (shiftLaw e ν)) :=
      integrable_u_rpow_iid hd (shiftLaw e ν) hr0.le hpow n 0
    rw [← law_map_xi (d := d) e ν] at hbase
    exact (integrable_map_measure hG.aestronglyMeasurable (hxim e).aemeasurable).mp hbase
  rw [hLHS, hmap 0]
  refine integral_mono (hInt 0) (hInt δ) fun η => ?_
  have hle : u (Parking.xi 0 η) n 0 ≤ u (Parking.xi δ η) n 0 := by
    refine u_mono_field hd (fun y => ?_) n 0
    simp only [Parking.xi]
    linarith
  rw [abs_of_nonneg (u_nonneg _ n 0), abs_of_nonneg (u_nonneg _ n 0)]
  exact Real.rpow_le_rpow (u_nonneg _ n 0) hle hr0.le

/-- **`eq:near-centered-moment` read at the particle law** (`parking.tex:2952-2955`).
"Since `η_δ ≤ ξ_δ`, monotonicity and `eq:near-centered-moment` bound
`(E u_n^δ(0)^r)^{1/r}`." -/
theorem exists_near_uNorm (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ m : ℕ, 2 ≤ m → ∀ j : ℕ,
      (∫ ω, |Parking.uOf ω m 0| ^ ((j : ℝ) + 2) ∂(Parking.law d (ν δ)))
            ^ (1 / ((j : ℝ) + 2))
        ≤ C * (phi d m + Real.sqrt ((j : ℝ) + 2) * l2Norm (green d m)
            + ((j : ℝ) + 2) * greenMax d m) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, -, -, hexp, -⟩ := hfam
  obtain ⟨C, hC, hCle⟩ := exists_near_centered (d := d) hd hGrowth hConc hfam'
  refine ⟨C, hC, fun δ hδ m hm j => ?_⟩
  haveI := hprob δ hδ
  have hr2 : (2 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hbridge := integral_uOf_rpow_le_xi (r := (j : ℝ) + 2) hd (ν δ) hθ (hexp δ hδ).1 hδ.1 (by linarith) m
  have hconv : ∫ η, |u (Parking.xi δ η) m 0| ^ ((j : ℝ) + 2) ∂(LatticeProb.iidLaw d (ν δ))
      = ∫ η, u (Parking.xi δ η) m 0 ^ (j + 2) ∂(LatticeProb.iidLaw d (ν δ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show |u (Parking.xi δ η) m 0| ^ ((j : ℝ) + 2) = u (Parking.xi δ η) m 0 ^ (j + 2)
    rw [abs_of_nonneg (u_nonneg _ m 0),
      show ((j : ℝ) + 2) = (((j + 2 : ℕ)) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hnn : (0 : ℝ) ≤ ∫ ω, |Parking.uOf ω m 0| ^ ((j : ℝ) + 2) ∂(Parking.law d (ν δ)) :=
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  rw [hconv] at hbridge
  refine le_trans (Real.rpow_le_rpow hnn hbridge (by positivity)) ?_
  exact hCle δ hδ m hm j

end Parking
end
