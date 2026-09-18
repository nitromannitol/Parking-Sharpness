/-
Theorem 1.7 of parking.tex, frozen.  `parking.tex:314-335` (label `thm:near`):

  "Let $\delta_0>0$.  For each $0\leq\delta\leq\delta_0$, let $\eta_\delta$ have
   i.i.d. integer-valued coordinates of mean $-\delta$.  Suppose that $\eta_0(0)$
   is nonconstant, that for some $\theta>0$ the expectations
   $\E e^{\theta|\eta_\delta(0)|}$ are bounded uniformly over $0\leq\delta\leq\delta_0$,
   and that for a constant $K<\infty$ and every $0<\delta\leq\delta_0$ the
   variables $\eta_\delta(0)$ and $\eta_0(0)$ admit a coupling with
   $\E|\eta_\delta(0)-\eta_0(0)|\leq K\delta$.  Then, as $\delta\downarrow0$,
   $\E U_\infty^\delta(0)\asymp\delta^{-3}, \delta^{-1}, \delta^{-1/3}$ in
   dimensions one, two, three, and $\asymp\log(e/\delta)$ for $d\geq4$."

A coupling is a probability measure on `ℤ × ℤ` with the two marginals.  The
asymptotic is written with constants and a threshold below which it holds;
the upper bound includes finiteness of `E U_∞^δ(0)`.  The uniform bound on the
exponential moments carries the integrability that makes it a bound on a
moment; without it the Bochner integral of a nonintegrable function is zero and
every family, however heavy tailed, would satisfy the hypothesis.  That
integrability also makes the mean condition a condition on a genuine mean, and
makes `∫|η_δ(0)-η_0(0)|` under the coupling a genuine expectation.

The results the proof quotes without proving them here enter as explicit
hypotheses.  The lower bound goes through `prop:near-divisible`, which carries
`thm:BP`, `lem:stopping-time`, `lem:u-concentration` and `eq:green-norms`; the
upper bound reads `eq:green-norms` again at the cutoff of `eq:near-cutoff` and
applies the Bernstein inequality of `prop:w-moment` at the near-critical law, so
standing ruling R1 attaches those five as explicit hypotheses.
-/
import Parking.Support.NearEndgame
import Parking.External.SandpileGrowth
import Parking.External.Stopping
import Parking.External.UConcentration
import Parking.External.GreenNorms
import Parking.External.Bernstein

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Parking.Frozen.near (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (hConcentration : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms) (hBernstein : Parking.External.Bernstein)
    (d : ℕ) (hd : 1 ≤ d) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (ν : ℝ → Measure ℤ)
    (hprob : ∀ δ ∈ Set.Icc 0 δ₀, IsProbabilityMeasure (ν δ))
    (hmean : ∀ δ ∈ Set.Icc 0 δ₀, ∫ k, (k : ℝ) ∂(ν δ) = -δ)
    (hnonconst : ∀ k : ℤ, ν 0 {k} ≠ 1)
    (θ M : ℝ) (hθ : 0 < θ)
    (hexp : ∀ δ ∈ Set.Icc 0 δ₀, Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) ∧
      ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M)
    (K : ℝ) (hcouple : ∀ δ ∈ Set.Ioc 0 δ₀, ∃ π : Measure (ℤ × ℤ), IsProbabilityMeasure π ∧
      π.map Prod.fst = ν δ ∧ π.map Prod.snd = ν 0 ∧
      ∫ p, |((p.1 : ℝ) - p.2)| ∂π ≤ K * δ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ ∈ Set.Ioc 0 δ₁,
      ENNReal.ofReal (c * Parking.nearRate d δ) ≤ Parking.meanUlimit (Parking.law d (ν δ)) ∧
        Parking.meanUlimit (Parking.law d (ν δ)) ≤ ENNReal.ofReal (C * Parking.nearRate d δ)
-- FROZEN-STATEMENT-END
:= by
  have hfam : Parking.NearFamily δ₀ ν θ M K :=
    ⟨hδ₀, hθ, hprob, hmean, hnonconst, hexp, hcouple⟩
  obtain ⟨c, δ₁, hc, hδ₁, -, hlow⟩ :=
    Parking.exists_rate_le_meanUlimit hd hGrowth hStopping hConcentration hGreen hfam
  obtain ⟨C, δ₂, hC, hδ₂, -, hup⟩ :=
    Parking.exists_meanUlimit_le_rate hd hGrowth hStopping hConcentration hBernstein
      hGreen hfam
  refine ⟨min c C, max c C, lt_min hc hC,
    le_trans (min_le_left _ _) (le_max_left _ _), min (min δ₁ δ₂) 1,
    lt_min (lt_min hδ₁ hδ₂) one_pos, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := le_trans hδ.2 (min_le_right _ _)
  have hδ₁' : δ ≤ δ₁ := le_trans hδ.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂' : δ ≤ δ₂ := le_trans hδ.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hR0 : (0 : ℝ) ≤ Parking.nearRate d δ := Parking.nearRate_nonneg d hδ0 hδ1
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow δ ⟨hδ0, hδ₁'⟩),
    le_trans (hup δ ⟨hδ0, hδ₂'⟩) (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_right (min_le_left _ _) hR0
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) hR0
