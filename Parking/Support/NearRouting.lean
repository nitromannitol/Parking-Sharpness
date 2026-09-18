/-
`eq:near-routing-mean` (`parking.tex:2938-2943`).

"Theorem 4.1, Lemma 5.1 and Proposition 5.6 give, for `n ≥ 2` and `r ≥ 2`,
`0 ≤ E U_n^δ(0) - E u_n^δ(0) ≤ C(n+1)^{1/r}(√(r κ_d(n)(E U_n^δ(0)^r)^{1/r}) + r)`.
The constants are uniform in `δ`."

The gap between the two mean odometers is at most twice the mean of the routing
discrepancy `w_n^⋆`, by the pathwise comparison, which holds wherever the instructions
are neighbours of the site carrying them, that is almost surely.  Jensen's inequality
raises that mean to the `r`-th moment norm, and `prop:w-moment` bounds the norm by the
`r`-th moment of the particle odometer itself.  Nothing in the chain uses the mean of
the one-site law, so the constant depends only on the dimension and on the exponential
moment, and in particular is uniform over a family of laws with a common moment bound.
-/
import Parking.Frozen.WMoment
import Parking.Frozen.PathwiseComparison
import Parking.Support.UpperTarget
import Parking.Support.NearTailSum
import Parking.Support.NearTiltInterval

open MeasureTheory LatticeProb

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **`eq:near-routing-mean`** (`parking.tex:2938-2943`).  The gap between the particle
and the divisible mean odometers is the mean of the routing discrepancy, which
`prop:w-moment` bounds by the moment of the particle odometer itself. -/
theorem exists_routing_mean (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexpabs : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      Parking.meanU (Parking.law d ν) n - Parking.meanu (Parking.law d ν) n
        ≤ C * ((n : ℝ) + 1) ^ (1 / r) *
          (Real.sqrt (r * Parking.kappa d n *
            (∫ ω, ((Parking.U ω n 0 : ℕ) : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r) := by
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν := integrable_abs_of_absMoment hθ hexpabs
  haveI hlawP : IsProbabilityMeasure (Parking.law d ν) := law_isProb hd ν
  obtain ⟨Cw, hCw, hw0⟩ := Parking.Frozen.w_moment hBern d hd
  have hw := hw0 ν inferInstance θ hθ hexp
  refine ⟨2 * Cw, by positivity, fun n hn r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  obtain ⟨hIw, hIws, hsup, hstar⟩ := hw n hn r hr
  -- the mean gap is at most twice the mean of the discrepancy
  have hIU : Integrable (fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ)) (Parking.law d ν) :=
    integrable_U_law hd ν hint n 0
  have hIu : Integrable (fun ω : Data d => Parking.uOf ω n 0) (Parking.law d ν) :=
    integrable_uOf hd ν hint n 0
  have hIwStar : Integrable (fun ω : Data d => Parking.wStar ω n 0) (Parking.law d ν) := by
    have h := integrable_wStar_rpow hd ν hθ hexp (le_refl (1 : ℝ)) n 0
    exact h.congr (Filter.Eventually.of_forall fun ω => Real.rpow_one _)
  have hgap : Parking.meanU (Parking.law d ν) n - Parking.meanu (Parking.law d ν) n
      ≤ 2 * ∫ ω, Parking.wStar ω n 0 ∂(Parking.law d ν) := by
    have hmono : ∫ ω, (((Parking.U ω n 0 : ℕ) : ℝ) - Parking.uOf ω n 0) ∂(Parking.law d ν)
        ≤ ∫ ω, (2 * Parking.wStar ω n 0) ∂(Parking.law d ν) := by
      refine integral_mono_ae (hIU.sub hIu) (hIwStar.const_mul 2) ?_
      refine (ae_stack_nbr_law hd ν).mono fun ω hω => ?_
      have hpath := (pathwise_comparison_of_labelOrder (d := d) hd hω n 0).2
      have hle := le_abs_self (((Parking.U ω n 0 : ℕ) : ℝ) - Parking.uOf ω n 0)
      linarith
    rw [integral_sub hIU hIu, integral_const_mul] at hmono
    exact hmono
  -- the mean of the discrepancy against its `r`-th moment
  have hjensen : ∫ ω, Parking.wStar ω n 0 ∂(Parking.law d ν)
      ≤ (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r) :=
    integral_le_rNorm (fun ω => wStar_nonneg ω n 0) hIwStar hr1 hIws
  have hpow0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 / r) := by
    refine Real.rpow_nonneg ?_ _
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hchain : (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r)
      ≤ ((n : ℝ) + 1) ^ (1 / r) * (Cw * (Real.sqrt (r * Parking.kappa d n *
          (∫ ω, ((Parking.U ω n 0 : ℕ) : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r)) :=
    le_trans hstar (mul_le_mul_of_nonneg_left hsup hpow0)
  nlinarith [hgap, hjensen, hchain, hpow0, hCw]

/-- **`eq:near-routing-mean` with a constant that does not depend on the law**
(`parking.tex:2938-2943`, "the constants are uniform in `δ`").  Only the first display
of `prop:w-moment` carries a constant, and that constant is a function of the dimension
alone, so one constant serves the whole family. -/
theorem exists_routing_mean_uniform (hd : 1 ≤ d) (hBern : Parking.External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      Parking.meanU (Parking.law d ν) n - Parking.meanu (Parking.law d ν) n
        ≤ C * ((n : ℝ) + 1) ^ (1 / r) *
          (Real.sqrt (r * Parking.kappa d n *
            (∫ ω, ((Parking.U ω n 0 : ℕ) : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r) := by
  obtain ⟨Cw, hCw, hwu⟩ := exists_wErr_moment_const_uniform (d := d) hd hBern
  refine ⟨2 * Cw, by positivity, ?_⟩
  intro ν hprobν θ hθ hexpabs n hn r hr
  haveI := hprobν
  have hexp := integrable_expMax_of_expAbs hθ hexpabs
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν := integrable_abs_of_absMoment hθ hexpabs
  haveI hlawP : IsProbabilityMeasure (Parking.law d ν) := law_isProb hd ν
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  obtain ⟨Cw', -, hw0'⟩ := Parking.Frozen.w_moment hBern d hd
  have hw' := hw0' ν inferInstance θ hθ hexp
  obtain ⟨hIw, hIws, -, hstar⟩ := hw' n hn r hr
  have hsup := hwu ν hprobν θ hθ hexp n hn r hr
  have hIU : Integrable (fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ)) (Parking.law d ν) :=
    integrable_U_law hd ν hint n 0
  have hIu : Integrable (fun ω : Data d => Parking.uOf ω n 0) (Parking.law d ν) :=
    integrable_uOf hd ν hint n 0
  have hIwStar : Integrable (fun ω : Data d => Parking.wStar ω n 0) (Parking.law d ν) := by
    have h := integrable_wStar_rpow hd ν hθ hexp (le_refl (1 : ℝ)) n 0
    exact h.congr (Filter.Eventually.of_forall fun ω => Real.rpow_one _)
  have hgap : Parking.meanU (Parking.law d ν) n - Parking.meanu (Parking.law d ν) n
      ≤ 2 * ∫ ω, Parking.wStar ω n 0 ∂(Parking.law d ν) := by
    have hmono : ∫ ω, (((Parking.U ω n 0 : ℕ) : ℝ) - Parking.uOf ω n 0) ∂(Parking.law d ν)
        ≤ ∫ ω, (2 * Parking.wStar ω n 0) ∂(Parking.law d ν) := by
      refine integral_mono_ae (hIU.sub hIu) (hIwStar.const_mul 2) ?_
      refine (ae_stack_nbr_law hd ν).mono fun ω hω => ?_
      have hpath := (pathwise_comparison_of_labelOrder (d := d) hd hω n 0).2
      have hle := le_abs_self (((Parking.U ω n 0 : ℕ) : ℝ) - Parking.uOf ω n 0)
      linarith
    rw [integral_sub hIU hIu, integral_const_mul] at hmono
    exact hmono
  have hjensen : ∫ ω, Parking.wStar ω n 0 ∂(Parking.law d ν)
      ≤ (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r) :=
    integral_le_rNorm (fun ω => wStar_nonneg ω n 0) hIwStar hr1 hIws
  have hpow0 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (1 / r) := by
    refine Real.rpow_nonneg ?_ _
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hchain : (∫ ω, Parking.wStar ω n 0 ^ r ∂(Parking.law d ν)) ^ (1 / r)
      ≤ ((n : ℝ) + 1) ^ (1 / r) * (Cw * (Real.sqrt (r * Parking.kappa d n *
          (∫ ω, ((Parking.U ω n 0 : ℕ) : ℝ) ^ r ∂(Parking.law d ν)) ^ (1 / r)) + r)) :=
    le_trans hstar (mul_le_mul_of_nonneg_left hsup hpow0)
  nlinarith [hgap, hjensen, hchain, hpow0, hCw]

end Parking
end
