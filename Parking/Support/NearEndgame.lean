/-
The arithmetic endgame of the near-critical upper bounds (`parking.tex:2944-2978`).

Step 3 at the near-critical law is Step 1 of `thm:upper`, whose constant is a function
of the dimension alone, followed by `eq:near-centered-moment` at the particle law.  At
the cutoff of `eq:near-cutoff` the exponent `r`, the walk factor `κ_d(N)` and the three
Green quantities are all bounded in the scale of `Parking/Support/NearProducts.lean`, so
`r κ_d(N) (E U_N^r)^{1/r}` is at most a constant multiple of the square of the rate, and
`eq:near-routing-mean` then bounds the gap between the two mean odometers by a constant
multiple of the rate itself.  The divisible mean is bounded by the rate by
`prop:near-divisible`, and Step 1 of the upper bounds carries the bound from the cutoff
to the limit.
-/
import Parking.Support.NearProducts
import Parking.Support.NearBridge
import Parking.Support.NearRouting
import Parking.Support.NearLowerLog
import Parking.Support.NearParticle
import Parking.Frozen.NearDivisible

open MeasureTheory

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **Step 3 at the near-critical law.**  The `r`-norm of the particle odometer at the
exponent `r = rHigh N`, with the four terms of `eq:near-moment`. -/
theorem exists_near_UNorm (hd : 1 ≤ d) (hGrowth : External.SandpileGrowth)
    (hConc : External.UConcentration) (hBern : External.Bernstein)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ N : ℕ, 2 ≤ N →
      (∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ)))
            ^ (1 / rHigh N)
        ≤ C * (phi d N + Real.sqrt (rHigh N) * l2Norm (green d N)
            + rHigh N * greenMax d N
            + rHigh N * kappa d N) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, -, -, hexp, -⟩ := hfam
  obtain ⟨C₁, hC₁, h1⟩ := upper_step_one_uniform (d := d) hd hBern
  obtain ⟨C₂, hC₂, h2⟩ := exists_near_uNorm hd hGrowth hConc hfam'
  refine ⟨C₁ * (1 + C₂) * Real.exp 2, by positivity, fun δ hδ N hN => ?_⟩
  haveI := hprob δ hδ
  have hexpabs := (hexp δ hδ).1
  have hexpmax := integrable_expMax_of_expAbs hθ hexpabs
  obtain ⟨j, hj⟩ := exists_rHigh_eq N
  have hr2 : (2 : ℝ) ≤ rHigh N := two_le_rHigh N
  have hr0 : (0 : ℝ) < rHigh N := by linarith
  have hA := h1 (ν δ) inferInstance θ hθ hexpmax N (by omega) (rHigh N) hr2
  have hB := h2 δ hδ N hN j
  rw [← hj] at hB
  have hnp : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  have he : ((N : ℝ) + 1) ^ (2 / rHigh N) ≤ Real.exp 2 :=
    rpow_two_div_le_exp_two hnp hr0 (log_le_rHigh N)
  set X : ℝ := (∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N
    ∂(law d (ν δ))) ^ (1 / rHigh N) with hXdef
  set Y : ℝ := (∫ ω, |uOf ω N 0| ^ rHigh N
    ∂(law d (ν δ))) ^ (1 / rHigh N) with hYdef
  set S : ℝ := phi d N
    + Real.sqrt (rHigh N) * l2Norm (green d N)
    + rHigh N * greenMax d N with hSdef
  set P : ℝ := rHigh N * kappa d N with hPdef
  have hphi0 : (0 : ℝ) ≤ phi d N := phi_nonneg' d N
  have hl20 : (0 : ℝ) ≤ Real.sqrt (rHigh N) * l2Norm (green d N) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmx0 : (0 : ℝ) ≤ rHigh N * greenMax d N :=
    mul_nonneg hr0.le (Real.iSup_nonneg fun x => green_nonneg N x)
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; linarith
  have hP0 : (0 : ℝ) ≤ P := mul_nonneg hr0.le (kappa_nonneg d N)
  have hexp1 : (1 : ℝ) ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hEK : rHigh N * ((N : ℝ) + 1) ^ (2 / rHigh N) * kappa d N
      ≤ Real.exp 2 * P := by
    have h := mul_le_mul_of_nonneg_left he hP0
    rw [hPdef] at h ⊢
    nlinarith [h]
  have hc1 : C₂ * S ≤ (1 + C₂) * Real.exp 2 * S := by
    have hcoef : C₂ ≤ (1 + C₂) * Real.exp 2 := by nlinarith [hexp1, hC₂.le]
    exact mul_le_mul_of_nonneg_right hcoef hS0
  have hc2 : Real.exp 2 * P ≤ (1 + C₂) * Real.exp 2 * P := by
    have hcoef : Real.exp 2 ≤ (1 + C₂) * Real.exp 2 := by nlinarith [hexp1, hC₂.le]
    exact mul_le_mul_of_nonneg_right hcoef hP0
  have hexpand : (1 + C₂) * Real.exp 2 * (S + P)
      = (1 + C₂) * Real.exp 2 * S + (1 + C₂) * Real.exp 2 * P := by ring
  have hstep : Y + rHigh N * ((N : ℝ) + 1) ^ (2 / rHigh N) * kappa d N
      ≤ (1 + C₂) * Real.exp 2 * (S + P) := by
    rw [hexpand]
    linarith [hB, hEK, hc1, hc2]
  have hgoal : X ≤ C₁ * (1 + C₂) * Real.exp 2 * (S + P) := by
    calc X ≤ C₁ * (Y + rHigh N * ((N : ℝ) + 1) ^ (2 / rHigh N)
              * kappa d N) := hA
      _ ≤ C₁ * ((1 + C₂) * Real.exp 2 * (S + P)) :=
          mul_le_mul_of_nonneg_left hstep hC₁.le
      _ = C₁ * (1 + C₂) * Real.exp 2 * (S + P) := by ring
  have hfinal : S + P = phi d N
      + Real.sqrt (rHigh N) * l2Norm (green d N)
      + rHigh N * greenMax d N
      + rHigh N * kappa d N := by rw [hSdef, hPdef]
  rw [← hfinal]
  exact hgoal

/-- The same with the two Green quantities replaced by their rates of `eq:green-norms`. -/
theorem exists_near_UNorm_rate (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hBern : Parking.External.Bernstein)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, ∀ N : ℕ, 2 ≤ N →
      (∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N)
        ≤ C * (phi d N + Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N
            + rHigh N * Parking.External.greenMaxRate d N + rHigh N * kappa d N) := by
  obtain ⟨C, hC, hCle⟩ := exists_near_UNorm hd hGrowth hConc hBern hfam
  obtain ⟨⟨cL, CL, hcL, hCL, hL⟩, ⟨cM, CM, hcM, hCM, hM⟩⟩ := hGreen d hd
  refine ⟨C * (1 + CL + CM), by positivity, fun δ hδ N hN => ?_⟩
  have h := hCle δ hδ N hN
  have hl := (hL N hN).2
  have hm := (hM N hN).2
  have hr0 : (0 : ℝ) < rHigh N := rHigh_pos N
  have hs0 : (0 : ℝ) ≤ Real.sqrt (rHigh N) := Real.sqrt_nonneg _
  have hphi0 : (0 : ℝ) ≤ phi d N := phi_nonneg' d N
  have hL0 : (0 : ℝ) ≤ Parking.External.greenL2Rate d N := greenL2Rate_nonneg d N
  have hM0 : (0 : ℝ) ≤ Parking.External.greenMaxRate d N := greenMaxRate_nonneg d N
  have hk0 : (0 : ℝ) ≤ kappa d N := kappa_nonneg d N
  have e1 : Real.sqrt (rHigh N) * l2Norm (green d N)
      ≤ CL * (Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N) := by
    nlinarith [mul_le_mul_of_nonneg_left hl hs0]
  have e2 : rHigh N * greenMax d N
      ≤ CM * (rHigh N * Parking.External.greenMaxRate d N) := by
    nlinarith [mul_le_mul_of_nonneg_left hm hr0.le]
  have t1 : (0 : ℝ) ≤ Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N :=
    mul_nonneg hs0 hL0
  have t2 : (0 : ℝ) ≤ rHigh N * Parking.External.greenMaxRate d N :=
    mul_nonneg hr0.le hM0
  have t3 : (0 : ℝ) ≤ rHigh N * kappa d N := mul_nonneg hr0.le hk0
  nlinarith [h, e1, e2, hphi0, t1, t2, t3, hC.le, hCL.le, hCM.le,
    mul_nonneg hC.le hphi0, mul_nonneg hC.le t1, mul_nonneg hC.le t2, mul_nonneg hC.le t3]

/-- **Step 3 at the cutoff.**  The product `r κ_d(N) (E U_N^r)^{1/r}` is at most a
constant multiple of the square of the rate, by the five products of
`Parking/Support/NearProducts.lean`. -/
theorem exists_rkappa_U_le (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hBern : Parking.External.Bernstein)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K)
    {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ ∈ Set.Icc (0 : ℝ) δ₀, 0 < δ → δ ≤ 1 → ∀ N : ℕ, 2 ≤ N →
      ((N : ℝ) ≤ C₀ * cutoffEnv d δ) →
      rHigh N * kappa d N *
          ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N))
        ≤ B * Parking.nearRate d δ ^ 2 := by
  obtain ⟨CU, hCU, hU⟩ := exists_near_UNorm_rate hd hGrowth hConc hBern hGreen hfam
  obtain ⟨A₃, hA₃, h₃⟩ := exists_prod_phi d hd hC₀
  obtain ⟨A₄, hA₄, h₄⟩ := exists_prod_greenL2 d hd hC₀
  obtain ⟨A₅, hA₅, h₅⟩ := exists_prod_greenMax d hC₀
  obtain ⟨A₆, hA₆, h₆⟩ := exists_prod_rkappa_sq d hC₀
  refine ⟨CU * (A₃ + A₄ + A₅ + A₆), by positivity, fun δ hδ hδ0 hδ1 N hN2 hNC => ?_⟩
  have hX := hU δ hδ N hN2
  have hP0 : (0 : ℝ) ≤ rHigh N * kappa d N :=
    mul_nonneg (rHigh_nonneg N) (kappa_nonneg d N)
  have hmul := mul_le_mul_of_nonneg_left hX hP0
  have hexpand : rHigh N * kappa d N *
        (CU * (phi d N + Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N
          + rHigh N * Parking.External.greenMaxRate d N + rHigh N * kappa d N))
      = CU * (rHigh N * kappa d N * phi d N
          + rHigh N * kappa d N *
              (Real.sqrt (rHigh N) * Parking.External.greenL2Rate d N)
          + rHigh N * kappa d N * (rHigh N * Parking.External.greenMaxRate d N)
          + rHigh N * kappa d N * (rHigh N * kappa d N)) := by ring
  rw [hexpand] at hmul
  have b₃ := h₃ N δ hδ0 hδ1 hN2 hNC
  have b₄ := h₄ N δ hδ0 hδ1 hN2 hNC
  have b₅ := h₅ N δ hδ0 hδ1 hN2 hNC
  have b₆ := h₆ N δ hδ0 hδ1 hN2 hNC
  nlinarith [hmul, b₃, b₄, b₅, b₆, hCU.le]

/-- **The near-critical upper bound.**  `E U_∞^δ(0) ≤ C R` for all small `δ`. -/
theorem exists_meanUlimit_le_rate (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping)
    (hConc : Parking.External.UConcentration) (hBern : Parking.External.Bernstein)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C δ₁ : ℝ, 0 < C ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁,
      Parking.meanUlimit (Parking.law d (ν δ))
        ≤ ENNReal.ofReal (C * Parking.nearRate d δ) := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, hnc, hexp, hcouple⟩ := id hfam
  obtain ⟨a, Ct, CR, δc, ha, hCt, hCR, hδc, hδcδ₀, hδc1, hcut⟩ :=
    exists_meanUlimit_le_cutoff hd hfam
  obtain ⟨C₀, hC₀, hNle⟩ := exists_nearCutoff_le d hCR ha
  obtain ⟨B, hB, hBle⟩ := exists_rkappa_U_le hd hGrowth hConc hBern hGreen hfam hC₀
  obtain ⟨A₁, hA₁, h₁⟩ := exists_prod_r (d := d) hC₀
  obtain ⟨CRt, hCRt, hrout⟩ := exists_routing_mean_uniform hd hBern
  obtain ⟨cD, CD, hcD, hCD, δd, hδd, hδdδ₀, hdiv⟩ :=
    Parking.Frozen.near_divisible hGrowth hStopping hConc hGreen d hd δ₀ ν θ M K hfam
  refine ⟨CRt * Real.exp 2 * (Real.sqrt B + A₁) + CD + Ct, min δc δd, by positivity,
    lt_min hδc hδd, le_trans (min_le_left _ _) hδcδ₀, fun δ hδ => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδc' : δ ≤ δc := le_trans hδ.2 (min_le_left _ _)
  have hδd' : δ ≤ δd := le_trans hδ.2 (min_le_right _ _)
  have hδ1 : δ ≤ 1 := le_trans hδc' hδc1
  have hδmem : δ ∈ Set.Icc (0 : ℝ) δ₀ := ⟨hδ0.le, le_trans hδc' hδcδ₀⟩
  haveI := hprob δ hδmem
  obtain ⟨hane, hcutδ⟩ := hcut δ ⟨hδ0, hδc'⟩
  set N : ℕ := nearCutoff d CR a δ with hNdef
  have haδ : 0 < a * δ ^ 2 := by positivity
  have hN2 : 2 ≤ N := two_le_nearCutoff d (resolventThreshold_pos d hCR haδ hane)
  have hNC : (N : ℝ) ≤ C₀ * cutoffEnv d δ := hNle δ hδ0 hδ1 hane
  have hR0 : (0 : ℝ) ≤ Parking.nearRate d δ := nearRate_nonneg d hδ0 hδ1
  have hR1 : (1 : ℝ) ≤ Parking.nearRate d δ := one_le_nearRate d hδ0 hδ1
  have hr0 : (0 : ℝ) < rHigh N := rHigh_pos N
  have hnp : (1 : ℝ) ≤ (N : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  -- the moment of the particle odometer at the cutoff
  have hrk := hBle δ hδmem hδ0 hδ1 N hN2 hNC
  have hr := h₁ N δ hδ0 hδ1 hN2 hNC
  -- the routing gap
  have hexpabs := (hexp δ hδmem).1
  have hro := hrout (ν δ) inferInstance θ hθ hexpabs N (by omega) (rHigh N) (two_le_rHigh N)
  have hE1 : ((N : ℝ) + 1) ^ (1 / rHigh N) ≤ Real.exp 2 :=
    le_trans (rpow_one_div_le_rpow_two_div hnp hr0)
      (rpow_two_div_le_exp_two hnp hr0 (log_le_rHigh N))
  have hE0 : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ (1 / rHigh N) := Real.rpow_nonneg (by linarith) _
  have hsq : Real.sqrt (rHigh N * kappa d N *
      ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N)))
      ≤ Real.sqrt B * Parking.nearRate d δ := by
    calc Real.sqrt (rHigh N * kappa d N *
          ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N)))
        ≤ Real.sqrt (B * Parking.nearRate d δ ^ 2) := Real.sqrt_le_sqrt hrk
      _ = Real.sqrt B * Parking.nearRate d δ := by
          rw [Real.sqrt_mul hB.le, Real.sqrt_sq hR0]
  have hsq0 : (0 : ℝ) ≤ Real.sqrt (rHigh N * kappa d N *
      ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N))) :=
    Real.sqrt_nonneg _
  have hgap : Parking.meanU (Parking.law d (ν δ)) N - Parking.meanu (Parking.law d (ν δ)) N
      ≤ CRt * Real.exp 2 * (Real.sqrt B + A₁) * Parking.nearRate d δ := by
    have hinner : Real.sqrt (rHigh N * kappa d N *
        ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N))) + rHigh N
        ≤ (Real.sqrt B + A₁) * Parking.nearRate d δ := by nlinarith [hsq, hr]
    have hprod : ((N : ℝ) + 1) ^ (1 / rHigh N) *
        (Real.sqrt (rHigh N * kappa d N *
          ((∫ ω, ((U ω N 0 : ℕ) : ℝ) ^ rHigh N ∂(law d (ν δ))) ^ (1 / rHigh N))) + rHigh N)
        ≤ Real.exp 2 * ((Real.sqrt B + A₁) * Parking.nearRate d δ) := by
      refine mul_le_mul hE1 hinner (by linarith [hsq0, hr0]) (Real.exp_pos 2).le
    nlinarith [hro, hprod, hCRt.le]
  -- the divisible mean at the cutoff
  have hmeanu : Parking.meanu (Parking.law d (ν δ)) N ≤ CD * Parking.nearRate d δ := by
    have h1 : ENNReal.ofReal (Parking.meanu (Parking.law d (ν δ)) N)
        ≤ ENNReal.ofReal (CD * Parking.nearRate d δ) :=
      le_trans (ofReal_meanu_le_meanuLimit N) (hdiv δ ⟨hδ0, hδd'⟩).1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hmeanU : Parking.meanU (Parking.law d (ν δ)) N
      ≤ (CRt * Real.exp 2 * (Real.sqrt B + A₁) + CD) * Parking.nearRate d δ := by
    nlinarith [hgap, hmeanu]
  refine le_trans hcutδ (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [hmeanU, hR1, hCt.le]

/-- **The near-critical lower bound.**  `c R ≤ E U_∞^δ(0)` for all small `δ`. -/
theorem exists_rate_le_meanUlimit (hd : 1 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) (hStopping : Parking.External.Stopping)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁,
      ENNReal.ofReal (c * Parking.nearRate d δ)
        ≤ Parking.meanUlimit (Parking.law d (ν δ)) := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, hnc, hexp, hcouple⟩ := id hfam
  by_cases h5 : 5 ≤ d
  · obtain ⟨c, δ₁, hc, hδ₁, hδ₁δ₀, hlow⟩ := exists_meanUlimit_log_lower hd hfam
    refine ⟨c, δ₁, hc, hδ₁, hδ₁δ₀, fun δ hδ => ?_⟩
    have hR : Parking.nearRate d δ = Real.log (Real.exp 1 / δ) := by
      rw [Parking.nearRate, if_neg (by omega : ¬ d = 1), if_neg (by omega : ¬ d = 2),
        if_neg (by omega : ¬ d = 3)]
    rw [hR]
    exact hlow δ hδ
  · obtain ⟨c, C, hc, hC, δ₁, hδ₁, hδ₁δ₀, hdiv⟩ :=
      Parking.Frozen.near_divisible hGrowth hStopping hConc hGreen d hd δ₀ ν θ M K hfam
    refine ⟨c, δ₁, hc, hδ₁, hδ₁δ₀, fun δ hδ => ?_⟩
    have hlow := (hdiv δ hδ).2.1 (by omega : d ≤ 4)
    haveI := hprob δ ⟨hδ.1.le, le_trans hδ.2 hδ₁δ₀⟩
    have hint : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
      integrable_abs_of_absMoment hθ (hexp δ ⟨hδ.1.le, le_trans hδ.2 hδ₁δ₀⟩).1
    exact le_trans hlow (meanuLimit_le_meanUlimit hd (ν δ) hint)

end Parking
end
