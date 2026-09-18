/-
Step 3 of `prop:near-divisible` (`parking.tex:2881-2896`), the matching upper bound
for a uniformly bounded family above dimension four.

The paper runs the whole of `lem:mean-horizon` a second time, at the rate
`ψ_d(s) = [log(s+2)]^{2/d}` instead of `φ_d`, for a family whose one-site laws
are supported in a fixed interval.  Three things change and nothing else does.

The reference law of Step 1 is the two point law at `±B` rather than the
symmetric Laplace law, because a mean zero law supported in `[-B,B]` is below it
in convex order (`Parking.convex_integral_le_twoPointLaw`).  The mean of the
odometer at that law is `C [log m]^{2/d}` by the bounded clause of `thm:BP`, and
the concentration term is a CONSTANT, because above dimension four both Green
rates of `eq:green-norms` are the constant one; a constant is below `ψ_d` since
`ψ_d ≥ [log 2]^{2/d}`.  Step 2 is the same block decomposition, run against
`ψ_d`, whose three properties it consumes are in
`Parking/Support/PsiRate.lean`.

The optimization at the end is the only genuinely different calculation.  Split
at `log(M+2) = 2log(e/δ)`.  Below it `ψ_d(M) ≤ 2[log(e/δ)]^{2/d}` and the drift
only helps.  Above it the horizon exceeds `(e/δ)^2`, so the drift is at least
`e^2/δ`, while `ψ_d(M) ≤ log(M+2) ≤ δ(M+2)/(2c₀) + log(2c₀/δ) - 1` and
`log(1/δ) ≤ 2\sqrt{1/δ}`, which the drift absorbs once `δ` is small.
-/
import Parking.Support.PsiRate

open MeasureTheory ProbabilityTheory LatticeProb
open scoped ENNReal NNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- A one-site law supported in `[-B,B]` gives a recentred law supported in
`[-(B+δ₀), B+δ₀]`. -/
theorem ae_abs_le_shiftLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] {B : ℤ} {δ δ₀ : ℝ}
    (hsupp : ν {k : ℤ | B < |k|} = 0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ₀) :
    ∀ᵐ z ∂(shiftLaw δ ν), |z| ≤ (B : ℝ) + δ₀ := by
  have hset : MeasurableSet {z : ℝ | |z| ≤ (B : ℝ) + δ₀} :=
    measurableSet_le (continuous_abs.measurable) measurable_const
  rw [shiftLaw, ae_map_iff (measurable_intShift δ).aemeasurable hset]
  have hae : ∀ᵐ k ∂ν, |k| ≤ B := by
    rw [ae_iff]
    have hEq : {k : ℤ | ¬ |k| ≤ B} = {k : ℤ | B < |k|} := by
      ext k; simp [not_le]
    rw [hEq]
    exact hsupp
  filter_upwards [hae] with k hk
  have hcast : |((k : ℤ) : ℝ)| ≤ (B : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hk
  have : |((k : ℤ) : ℝ) + δ| ≤ |((k : ℤ) : ℝ)| + |δ| := abs_add_le _ _
  rw [abs_of_nonneg hδ0] at this
  linarith

/-- **The coordinate replacement of Step 3.**  Every moment of the odometer of the recentred
scenery of a uniformly bounded family is below the same moment at the two point law. -/
theorem integral_pow_u_xi_le_twoPoint (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {Bd : ℝ} (hB : 0 < Bd) {δ : ℝ}
    (hbound : ∀ᵐ z ∂(shiftLaw δ (ν δ)), |z| ≤ Bd)
    (hδ : δ ∈ Set.Icc (0:ℝ) δ₀) (k m : ℕ) :
    ∫ η, u (Parking.xi δ η) m 0 ^ (k + 2) ∂(LatticeProb.iidLaw d (ν δ))
      ≤ ∫ η, u η m 0 ^ (k + 2)
          ∂(LatticeProb.iidLaw d (twoPointLaw Bd)) := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδ).1
  have hintid : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) hintexp
  set μ : Measure ℝ := shiftLaw δ (ν δ) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hμmean : ∫ z, z ∂μ = 0 := by
    rw [hμ, integral_shiftLaw_id δ (ν δ) hintid, hmeanν δ hδ]
    ring
  have hμid : Integrable (id : ℝ → ℝ) μ := by
    rw [hμ]; exact integrable_id_shiftLaw δ (ν δ) hintid
  have hbdd : ∀ᵐ z ∂μ, |z| ≤ Bd := by rw [hμ]; exact hbound
  have hcomp : ∀ (f : ℝ → ℝ) (Kf : NNReal), ConvexOn ℝ Set.univ f → LipschitzWith Kf f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂(twoPointLaw Bd) := fun f Kf hf hfL =>
    convex_integral_le_twoPointLaw hB hbdd hμid hμmean hf hfL
  have hζid : Integrable (id : ℝ → ℝ) (twoPointLaw Bd) := integrable_twoPointLaw _ _
  have hIζ : Integrable (fun η : Site d → ℝ => u η m 0 ^ (k + 2))
      (LatticeProb.iidLaw d (twoPointLaw Bd)) :=
    integrable_u_pow_iid hd _ (k + 2) (integrable_twoPointLaw _ _) m 0
  have hxim : Measurable (fun η : Site d → ℤ => Parking.xi δ η) :=
    measurable_pi_lambda _ fun y =>
      (measurable_intCastReal.comp (measurable_pi_apply y)).add_const δ
  have hmapped : ∫ η, u η m 0 ^ (k + 2) ∂(LatticeProb.iidLaw d μ)
      = ∫ η, u (Parking.xi δ η) m 0 ^ (k + 2) ∂(LatticeProb.iidLaw d (ν δ)) := by
    rw [hμ, ← law_map_xi (d := d) δ (ν δ)]
    exact integral_map hxim.aemeasurable
      ((measurable_u_eval m 0).pow_const (k + 2)).aestronglyMeasurable
  rw [← hmapped]
  exact integral_pow_u_iid_le hd hμid hζid hcomp k m 0 hIζ

theorem psi_pos (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 < psi d s :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le (Real.log_pos (by norm_num))
    (log_two_le_log_add_two hs)) _

theorem log_two_rpow_le_psi (d : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    Real.log 2 ^ ((2:ℝ) / d) ≤ psi d s :=
  Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) (log_two_le_log_add_two hs) (by positivity)

theorem log_rpow_le_psi (d : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    Real.log m ^ ((2:ℝ) / d) ≤ psi d m := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  exact Real.rpow_le_rpow (Real.log_nonneg hm1)
    (Real.log_le_log (by linarith) (by linarith)) (by positivity)

/-- **`thm:BP` at a bounded law above dimension four**, read against the rate `ψ_d`. -/
theorem exists_mean_le_psi (hd5 : 5 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (hmean : ∫ z, z ∂ζ = 0) (hv0 : 0 < evariance id ζ) (hvT : evariance id ζ < ⊤)
    (hexp : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun z : ℝ => Real.exp (θ * |z|)) ζ)
    (hbdd : ∃ b : ℝ, ∀ᵐ z ∂ζ, b ≤ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Parking.External.meanSandpileReal d ζ m ≤ C * psi d m := by
  have hd : 1 ≤ d := by omega
  obtain ⟨-, -, -, h5b, -⟩ := hGrowth d hd ζ inferInstance hmean hv0 hvT hexp
  obtain ⟨c, C, hc, hC, h⟩ := h5b hd5 hbdd
  refine ⟨C, hC, fun m hm => ?_⟩
  refine le_trans (h m hm).2 ?_
  exact mul_le_mul_of_nonneg_left (log_rpow_le_psi d (by omega)) hC.le

/-- **Step 3's moment bound at a bounded reference law** (`parking.tex:2884-2888`).  Above
dimension four both Green rates are constant, so the concentration term is a constant and
the fifth moment norm of the odometer is at most a multiple of `ψ_d(m)`. -/
theorem exists_psi_moment (hd5 : 5 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (hmean : ∫ z, z ∂ζ = 0) (hv0 : 0 < evariance id ζ) (hvT : evariance id ζ < ⊤)
    {θ' : ℝ} (hθ' : 0 < θ') (hexp' : Integrable (fun z : ℝ => Real.exp (θ' * |z|)) ζ)
    (hbdd : ∃ b : ℝ, ∀ᵐ z ∂ζ, b ≤ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      (∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d ζ)) ^ ((1:ℝ)/5) ≤ C * psi d m := by
  classical
  have hd : 1 ≤ d := by omega
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ζ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ζ))
  obtain ⟨C0, hC0, hmeanle⟩ :=
    exists_mean_le_psi hd5 hGrowth ζ hmean hv0 hvT ⟨θ', hθ', hexp'⟩ hbdd
  obtain ⟨C1, hC1, hnorm⟩ := exists_uNormReal_le (d := d) hd hConc ζ hθ' hexp'
  obtain ⟨⟨c2, C2, hc2, hC2, hg2⟩, ⟨c3, C3, hc3, hC3, hg3⟩⟩ := hGreen d hd
  have hrate2 : ∀ n : ℕ, Parking.External.greenL2Rate d n = 1 := by
    intro n
    rw [Parking.External.greenL2Rate, if_neg (by omega : ¬ d = 1),
      if_neg (by omega : ¬ d = 2), if_neg (by omega : ¬ d = 3), if_neg (by omega : ¬ d = 4)]
  have hrate3 : ∀ n : ℕ, Parking.External.greenMaxRate d n = 1 := by
    intro n
    rw [Parking.External.greenMaxRate, if_neg (by omega : ¬ d = 1),
      if_neg (by omega : ¬ d = 2)]
  have hmaxpow : Integrable (fun t : ℝ => max t 0 ^ (⌈(5:ℝ)⌉₊)) ζ :=
    integrable_maxPow_of_exp ζ hθ' hexp' _
  have hI : ∀ m : ℕ, Integrable (fun η : Site d → ℝ => |u η m 0| ^ (5:ℝ))
      (LatticeProb.iidLaw d ζ) :=
    fun m => integrable_u_rpow_iid hd ζ (by norm_num) hmaxpow m 0
  set Z : ℕ → ℝ := fun m => ∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d ζ) with hZ
  have hZ0 : ∀ m, 0 ≤ Z m := fun m =>
    integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _
  set L : ℝ := Real.log 2 ^ ((2:ℝ) / d) with hL
  have hL0 : 0 < L := Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  set Cm : ℝ := C0 + C1 * (Real.sqrt 5 * C2 + 5 * C3) / L with hCm
  have hCm0 : 0 < Cm := by
    have hpos : 0 < C1 * (Real.sqrt 5 * C2 + 5 * C3) / L := by
      have : (0:ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    linarith
  have hmain : ∀ m : ℕ, 2 ≤ m → Z m ^ ((1:ℝ)/5) ≤ Cm * psi d m := by
    intro m hm
    have h1 := hnorm m (by omega) 5 (by norm_num)
    have h2 := hmeanle m hm
    have h3 := (hg2 m hm).2
    have h4 := (hg3 m hm).2
    rw [hrate2 m, mul_one] at h3
    rw [hrate3 m, mul_one] at h4
    have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hLpsi : L ≤ psi d m := log_two_rpow_le_psi d hmnn
    have hs5 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hl20 : 0 ≤ l2Norm (green d m) := Real.sqrt_nonneg _
    have hmx0 : (0 : ℝ) ≤ greenMax d m := Real.iSup_nonneg fun x => green_nonneg m x
    have hconc : C1 * (Real.sqrt 5 * l2Norm (green d m) + 5 * greenMax d m)
        ≤ C1 * (Real.sqrt 5 * C2 + 5 * C3) := by
      refine mul_le_mul_of_nonneg_left ?_ hC1.le
      have e1 : Real.sqrt 5 * l2Norm (green d m) ≤ Real.sqrt 5 * C2 :=
        mul_le_mul_of_nonneg_left h3 hs5
      linarith
    have hpos : (0:ℝ) ≤ C1 * (Real.sqrt 5 * C2 + 5 * C3) := by positivity
    have habs : C1 * (Real.sqrt 5 * C2 + 5 * C3)
        ≤ C1 * (Real.sqrt 5 * C2 + 5 * C3) / L * psi d m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
      nlinarith [hLpsi, hpos]
    calc Z m ^ ((1:ℝ)/5) ≤ Parking.External.meanSandpileReal d ζ m
            + C1 * (Real.sqrt 5 * l2Norm (green d m) + 5 * greenMax d m) := h1
      _ ≤ Cm * psi d m := by rw [hCm]; nlinarith [h2, hconc, habs]
  have hmono : ∀ m : ℕ, m ≤ 2 → Z m ≤ Z 2 := by
    intro m hm
    refine integral_mono (hI m) (hI 2) fun η => ?_
    have hle : u η m 0 ≤ u η 2 0 := u_monotone_time hd η 0 hm
    rw [abs_of_nonneg (u_nonneg η m 0), abs_of_nonneg (u_nonneg η 2 0)]
    exact Real.rpow_le_rpow (u_nonneg η m 0) hle (by norm_num)
  refine ⟨max Cm (Cm * psi d 2 / L), lt_of_lt_of_le hCm0 (le_max_left _ _), fun m => ?_⟩
  have hmnn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
  have hpsi0 : 0 < psi d m := psi_pos d hmnn
  by_cases hm : 2 ≤ m
  · exact le_trans (hmain m hm) (mul_le_mul_of_nonneg_right (le_max_left _ _) hpsi0.le)
  · have hm2 : m ≤ 2 := by omega
    have ha : Z m ^ ((1:ℝ)/5) ≤ Z 2 ^ ((1:ℝ)/5) :=
      Real.rpow_le_rpow (hZ0 m) (hmono m hm2) (by norm_num)
    have hb : Z 2 ^ ((1:ℝ)/5) ≤ Cm * psi d 2 := hmain 2 le_rfl
    have hc : L ≤ psi d m := log_two_rpow_le_psi d hmnn
    have hd2 : 0 ≤ Cm * psi d ((2:ℕ) : ℝ) := by
      have : 0 < psi d ((2:ℕ) : ℝ) := psi_pos d (by positivity)
      positivity
    have he : Cm * psi d ((2:ℕ) : ℝ) ≤ Cm * psi d ((2:ℕ) : ℝ) / L * psi d m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
      nlinarith [hc, hd2]
    have hf : Cm * psi d ((2:ℕ) : ℝ) / L * psi d m
        ≤ max Cm (Cm * psi d ((2:ℕ) : ℝ) / L) * psi d m :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hpsi0.le
    linarith

/-- **Step 1 of the mean horizon lemma at the rate of Step 3.**  For a uniformly bounded
family the fifth moment norm of the odometer of the recentred scenery is at most
`C ψ_d(m)`, uniformly in `δ`. -/
theorem exists_step1_psi (hd5 : 5 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K)
    {B : ℤ} (hsupp : ∀ δ' ∈ Set.Icc (0:ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, ∀ m : ℕ,
      (∫ η, u (Parking.xi δ η) m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (ν δ))) ^ ((1:ℝ)/5)
        ≤ C * psi d m := by
  have hd : 1 ≤ d := by omega
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  set Bd : ℝ := max ((B : ℝ) + δ₀) 1 with hBd
  have hB0 : 0 < Bd := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hζmean : ∫ z, z ∂(twoPointLaw Bd) = 0 := integral_twoPointLaw_id Bd
  have hζv0 : 0 < evariance (id : ℝ → ℝ) (twoPointLaw Bd) := evariance_twoPointLaw_pos hB0
  have hζvT : evariance (id : ℝ → ℝ) (twoPointLaw Bd) < ⊤ := evariance_twoPointLaw_lt_top Bd
  have hζexp : Integrable (fun z : ℝ => Real.exp (1 * |z|)) (twoPointLaw Bd) :=
    integrable_twoPointLaw Bd _
  have hζbdd : ∃ b : ℝ, ∀ᵐ z ∂(twoPointLaw Bd), b ≤ z := ⟨-|Bd|, ae_neg_le_twoPointLaw Bd⟩
  obtain ⟨C, hC, hCle⟩ := exists_psi_moment (d := d) hd5 hGrowth hConc hGreen (twoPointLaw Bd)
    hζmean hζv0 hζvT one_pos hζexp hζbdd
  refine ⟨C, hC, fun δ hδ m => ?_⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hconv : ∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d (twoPointLaw Bd))
      = ∫ η, u η m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (twoPointLaw Bd)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show |u η m 0| ^ (5:ℝ) = u η m 0 ^ (5:ℕ)
    rw [abs_of_nonneg (u_nonneg η m 0), show (5:ℝ) = ((5:ℕ):ℝ) by norm_num,
      Real.rpow_natCast]
  have hbound : ∀ᵐ z ∂(shiftLaw δ (ν δ)), |z| ≤ Bd := by
    filter_upwards [ae_abs_le_shiftLaw (ν δ) (hsupp δ hδ) hδ.1 hδ.2] with z hz
    exact le_trans hz (le_max_left _ _)
  have hcmp := integral_pow_u_xi_le_twoPoint (d := d) hd hfam' hB0 hbound hδ 3 m
  have h5 : (3 : ℕ) + 2 = 5 := by norm_num
  rw [h5] at hcmp
  have hnn : (0:ℝ) ≤ ∫ η, u (Parking.xi δ η) m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (ν δ)) :=
    integral_nonneg fun η => pow_nonneg (u_nonneg _ m 0) _
  refine le_trans (Real.rpow_le_rpow hnn hcmp (by norm_num)) ?_
  rw [← hconv]
  exact hCle m

/-- **`lem:mean-horizon` at the rate of Step 3** (`parking.tex:2888-2890`).  The block
decomposition of Step 2 of that lemma, run at the rate `ψ_d` instead of `φ_d`: the three
properties of the scale it consumes are nonnegativity, `ψ_d(M+2) ≤ 3ψ_d(M)` and the
convergence of the dyadic series, and `Parking/Support/PsiRate.lean` supplies all three. -/
theorem exists_meanHorizon_psi (hd5 : 5 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hStopping : Parking.External.Stopping) (hConc : Parking.External.UConcentration)
    (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K)
    {B : ℤ} (hsupp : ∀ δ' ∈ Set.Icc (0:ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, ∀ n : ℕ,
      ∀ σ : (Site d → ℤ) → (ℕ → Site d) → ℕ,
        (∀ η, LatticeProb.IsWalkStopping (σ η)) → (∀ η X, σ η X ≤ n) →
        (∀ X, Measurable fun η => σ η X) →
        ∀ Mσ : ℝ, Mσ = ∫ η, ∫ X, ((σ η X : ℕ) : ℝ)
              ∂(LatticeProb.siteWalkLaw d (0 : Site d)) ∂(LatticeProb.iidLaw d (ν δ)) →
          Integrable (rewardAvg δ σ) (LatticeProb.iidLaw d (ν δ)) ∧
            ∫ η, rewardAvg δ σ η ∂(LatticeProb.iidLaw d (ν δ)) ≤ C * psi d Mσ := by
  classical
  have hd : 1 ≤ d := by omega
  haveI : NeZero d := ⟨by omega⟩
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexpfam, -⟩ := id hfam
  obtain ⟨C1, hC1, hstep1⟩ := exists_step1_psi hd5 hGrowth hConc hGreen hfam' hsupp
  obtain ⟨C2, hC2, hseries⟩ := exists_psi_block_sum d (by omega : 2 ≤ d)
  refine ⟨3 * C1 * (1 + C2), by positivity, fun δ hδ n σ hσ hσn hm Mσ hMdef => ?_⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexpfam δ hδ).1
  set P := LatticeProb.iidLaw d (ν δ) with hP
  haveI : IsProbabilityMeasure P := by rw [hP, LatticeProb.iidLaw]; infer_instance
  have hIreward : Integrable (rewardAvg δ σ) P :=
    integrable_rewardAvg hd hθ (ν δ) hexp hσ hσn hm
  refine ⟨hIreward, ?_⟩
  have hM0 : 0 ≤ Mσ := by
    rw [hMdef]
    exact integral_nonneg fun η => integral_nonneg fun X => Nat.cast_nonneg _
  set N : ℕ := max 1 ⌈Mσ⌉₊ with hNdef
  have hN1 : 1 ≤ N := le_max_left 1 _
  obtain ⟨hNM, hNM2⟩ := ceil_bounds hM0
  rw [← hNdef] at hNM hNM2
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    linarith
  have hblocks : ∀ η, rewardAvg δ σ η ≤ ∑ k ∈ Finset.range (n + 1), blockAvg δ σ N k η := by
    intro η
    exact integral_stopping_reward_le hd hStopping (Parking.xi δ η) (hσ η) (hσn η) hN1
  have hIsum : Integrable (fun η => ∑ k ∈ Finset.range (n + 1), blockAvg δ σ N k η) P :=
    integrable_finsetSum _ fun k _ => integrable_blockAvg hd hθ (ν δ) hexp hσ hσn hm N k
  have hchain1 : ∫ η, rewardAvg δ σ η ∂P
      ≤ ∑ k ∈ Finset.range (n + 1), ∫ η, blockAvg δ σ N k η ∂P := by
    rw [← integral_finsetSum _ (fun k _ => integrable_blockAvg hd hθ (ν δ) hexp hσ hσn hm N k)]
    exact integral_mono hIreward hIsum hblocks
  refine hchain1.trans ?_
  have hpsiMnn : 0 ≤ psi d Mσ := psi_nonneg d hM0
  have hpsiN3 : psi d ((N:ℕ):ℝ) ≤ 3 * psi d Mσ :=
    le_trans (psi_mono d (by positivity : (0:ℝ) ≤ ((N:ℕ):ℝ)) hNM2)
      (psi_add_two_le d (by omega : 2 ≤ d) hM0)
  have hpsiNnn : 0 ≤ psi d ((N:ℕ):ℝ) := psi_nonneg d (by positivity)
  have hterm : ∀ k : ℕ, ∫ η, blockAvg δ σ N k η ∂P
      ≤ ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N k))) ^ ((4:ℝ)/5)
        * (C1 * psi d (((blockBound N (k + 1) - blockBound N k : ℕ) : ℝ))) := by
    intro k
    refine (integral_blockAvg_le hd hθ (ν δ) hexp hσ hσn hm N k).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg measureReal_nonneg _)
    exact hstep1 δ hδ _
  have hzero : ∫ η, blockAvg δ σ N 0 η ∂P ≤ C1 * psi d ((N:ℕ):ℝ) := by
    refine (hterm 0).trans ?_
    rw [blockLen_zero N]
    have h1 : ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N 0))) ^ ((4:ℝ)/5) ≤ 1 :=
      Real.rpow_le_one measureReal_nonneg
        (measureReal_blockEvent_le_one hd (ν δ) σ _) (by norm_num)
    have h2 : (0:ℝ) ≤ C1 * psi d ((N:ℕ):ℝ) := by positivity
    calc ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N 0))) ^ ((4:ℝ)/5)
          * (C1 * psi d ((N:ℕ):ℝ))
        ≤ 1 * (C1 * psi d ((N:ℕ):ℝ)) := mul_le_mul_of_nonneg_right h1 h2
      _ = C1 * psi d ((N:ℕ):ℝ) := one_mul _
  have hsucc : ∀ j : ℕ, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * ((N:ℕ):ℝ))) := by
    intro j
    have hb : blockBound N (j + 1) = 2 ^ j * N := blockBound_succ_eq N hN1 j
    have hbpos : 0 < blockBound N (j + 1) := by
      rw [hb]; exact Nat.mul_pos (Nat.two_pow_pos j) hN1
    have hbR : ((blockBound N (j + 1) : ℕ) : ℝ) = 2 ^ j * ((N:ℕ):ℝ) := by
      rw [hb]; push_cast; ring
    have hmk := measureReal_blockEvent_le hd (ν δ) hσ hσn hm (s := blockBound N (j + 1)) hbpos
    rw [← hMdef, hbR] at hmk
    have h2j : (0:ℝ) < (2:ℝ) ^ j := by positivity
    have hle : (jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))
        ≤ (2:ℝ) ^ (-(j:ℝ)) := by
      refine hmk.trans ?_
      rw [div_le_iff₀ (by positivity), Real.rpow_neg (by norm_num), Real.rpow_natCast]
      rw [inv_mul_eq_div, le_div_iff₀ h2j]
      nlinarith [hNM, hNpos, h2j]
    have hrpow : ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))) ^ ((4:ℝ)/5)
        ≤ (2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) := by
      refine le_trans (Real.rpow_le_rpow measureReal_nonneg hle (by norm_num)) ?_
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    refine (hterm (j + 1)).trans ?_
    rw [blockLen_succ N hN1 j]
    have hcast : (((2 ^ j * N : ℕ)) : ℝ) = 2 ^ j * ((N:ℕ):ℝ) := by push_cast; ring
    rw [hcast]
    have hpsij : 0 ≤ psi d (2 ^ j * ((N:ℕ):ℝ)) := psi_nonneg d (by positivity)
    have h2 : (0:ℝ) ≤ C1 * psi d (2 ^ j * ((N:ℕ):ℝ)) := by positivity
    calc ((jointLaw d (ν δ)).real (blockEvent σ (blockBound N (j + 1)))) ^ ((4:ℝ)/5)
          * (C1 * psi d (2 ^ j * ((N:ℕ):ℝ)))
        ≤ (2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * (C1 * psi d (2 ^ j * ((N:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_right hrpow h2
      _ = C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * ((N:ℕ):ℝ))) := by ring
  have hN1R : (1:ℝ) ≤ ((N:ℕ):ℝ) := by exact_mod_cast hN1
  obtain ⟨hsummable, htsum⟩ := hseries ((N:ℕ):ℝ) hN1R
  have hfin : ∑ j ∈ Finset.range n,
      ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * ((N:ℕ):ℝ)))
      ≤ C2 * psi d ((N:ℕ):ℝ) := by
    refine le_trans (Summable.sum_le_tsum _ (fun j _ => ?_) hsummable) htsum
    have : 0 ≤ psi d (2 ^ j * ((N:ℕ):ℝ)) := psi_nonneg d (by positivity)
    positivity
  rw [Finset.sum_range_succ']
  have hsum2 : ∑ j ∈ Finset.range n, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ ∑ j ∈ Finset.range n,
        C1 * ((2:ℝ) ^ (-(j:ℝ) * ((4:ℝ)/5)) * psi d (2 ^ j * ((N:ℕ):ℝ))) :=
    Finset.sum_le_sum fun j _ => hsucc j
  rw [← Finset.mul_sum] at hsum2
  have hA : ∑ j ∈ Finset.range n, ∫ η, blockAvg δ σ N (j + 1) η ∂P
      ≤ C1 * (C2 * psi d ((N:ℕ):ℝ)) :=
    hsum2.trans (mul_le_mul_of_nonneg_left hfin hC1.le)
  have hD : C1 * (1 + C2) * psi d ((N:ℕ):ℝ) ≤ 3 * C1 * (1 + C2) * psi d Mσ := by
    have h1 : (0:ℝ) ≤ C1 * (1 + C2) := by positivity
    nlinarith [hpsiN3, h1]
  nlinarith [hA, hzero, hD]

/-- **The optimization over the mean horizon at the rate of Step 3**
(`parking.tex:2894-2896`).  Subtracting the drift from `c₀ ψ_d(M)` and taking the supremum
over `M ≥ 0` leaves `C [log(e/δ)]^{2/d}`. -/
theorem exists_psi_sub_le (d : ℕ) (hd5 : 5 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C δ₂ : ℝ, 0 < C ∧ 0 < δ₂ ∧ δ₂ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ Mv : ℝ, 0 ≤ Mv →
      c₀ * psi d Mv - δ * Mv ≤ C * Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d) := by
  have hd2 : 2 ≤ d := by omega
  set C : ℝ := 2 * c₀ + 2 + c₀ * |Real.log (2 * c₀)| with hCdef
  have hC0 : 0 < C := by positivity
  set δ₂ : ℝ := min 1 (Real.exp 1 ^ 4 / (16 * c₀ ^ 2)) with hδ₂def
  have hδ₂0 : 0 < δ₂ := lt_min one_pos (by positivity)
  refine ⟨C, δ₂, hC0, hδ₂0, min_le_left _ _, ?_⟩
  intro δ hδ0 hδle Mv hMv
  have hδ1 : δ ≤ 1 := le_trans hδle (min_le_left _ _)
  have hδs : δ ≤ Real.exp 1 ^ 4 / (16 * c₀ ^ 2) := le_trans hδle (min_le_right _ _)
  have hEδ : 0 < Real.exp 1 / δ := by positivity
  set P : ℝ := Real.log (Real.exp 1 / δ) with hPdef
  have hP1 : (1:ℝ) ≤ P := by
    rw [hPdef, Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hδ0), Real.log_exp]
    have := Real.log_nonpos (by linarith) hδ1
    linarith
  have hPrp : (1:ℝ) ≤ P ^ ((2:ℝ) / d) := Real.one_le_rpow hP1 (by positivity)
  have hLnn : (0:ℝ) ≤ Real.log (Mv + 2) := log_add_two_nonneg hMv
  by_cases hreg : Real.log (Mv + 2) ≤ 2 * P
  · have h1 : psi d Mv ≤ (2 * P) ^ ((2:ℝ) / d) :=
      Real.rpow_le_rpow hLnn hreg (by positivity)
    have h2 : (2 * P) ^ ((2:ℝ) / d) = (2:ℝ) ^ ((2:ℝ) / d) * P ^ ((2:ℝ) / d) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3 : (2:ℝ) ^ ((2:ℝ) / d) ≤ 2 := two_rpow_le_two hd2
    have h4 : psi d Mv ≤ 2 * P ^ ((2:ℝ) / d) := by
      rw [h2] at h1
      nlinarith [h1, h3, hPrp]
    have h5 : 0 ≤ δ * Mv := by positivity
    have h6 : c₀ * psi d Mv ≤ 2 * c₀ * P ^ ((2:ℝ) / d) := by nlinarith [h4, hc₀]
    have h7 : 2 * c₀ ≤ C := by
      rw [hCdef]
      nlinarith [abs_nonneg (Real.log (2 * c₀)), hc₀]
    have h8 : 2 * c₀ * P ^ ((2:ℝ) / d) ≤ C * P ^ ((2:ℝ) / d) :=
      mul_le_mul_of_nonneg_right h7 (by linarith)
    linarith
  · replace hreg : 2 * P < Real.log (Mv + 2) := not_le.mp hreg
    have hL1 : (1:ℝ) ≤ Real.log (Mv + 2) := by linarith
    have hpsile : psi d Mv ≤ Real.log (Mv + 2) := rpow_le_self_of_one_le hd2 hL1
    -- the horizon is beyond `(e/δ)^2`
    have hbig : (Real.exp 1 / δ) ^ 2 < Mv + 2 := by
      have hlt : Real.log ((Real.exp 1 / δ) ^ 2) < Real.log (Mv + 2) := by
        rw [Real.log_pow]
        push_cast
        linarith [hreg]
      exact (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlt
    have hdM : Real.exp 1 ^ 2 / δ - 2 * δ < δ * Mv := by
      have hexp : (Real.exp 1 / δ) ^ 2 = Real.exp 1 ^ 2 / δ ^ 2 := by rw [div_pow]
      rw [hexp] at hbig
      have h := mul_lt_mul_of_pos_left hbig hδ0
      have he : δ * (Real.exp 1 ^ 2 / δ ^ 2) = Real.exp 1 ^ 2 / δ := by field_simp
      rw [he] at h
      linarith
    -- the logarithm bound
    have hlogbound : c₀ * Real.log (Mv + 2)
        ≤ δ * (Mv + 2) / 2 + c₀ * Real.log (2 * c₀ / δ) - c₀ := by
      have h := log_le_div_add (Mv + 2) (2 * c₀ / δ) (by linarith) (by positivity)
      have hdiv : (Mv + 2) / (2 * c₀ / δ) = δ * (Mv + 2) / (2 * c₀) := by
        field_simp
      rw [hdiv] at h
      have hmul := mul_le_mul_of_nonneg_left h hc₀.le
      have he : c₀ * (δ * (Mv + 2) / (2 * c₀) + Real.log (2 * c₀ / δ) - 1)
          = δ * (Mv + 2) / 2 + c₀ * Real.log (2 * c₀ / δ) - c₀ := by
        field_simp
      linarith [hmul, he.le, he.ge]
    -- the logarithm of the drift
    have hsplit : Real.log (2 * c₀ / δ) = Real.log (2 * c₀) + Real.log (1 / δ) := by
      rw [Real.log_div (by positivity) (ne_of_gt hδ0), Real.log_div one_ne_zero (ne_of_gt hδ0),
        Real.log_one]
      ring
    have hsqrt : Real.log (1 / δ) ≤ 2 * Real.sqrt (1 / δ) := log_le_two_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (1 / δ) := Real.sqrt_pos.mpr (by positivity)
    have hssq : Real.sqrt (1 / δ) ^ 2 = 1 / δ := Real.sq_sqrt (by positivity)
    have hepos : (0:ℝ) < Real.exp 1 ^ 2 := by positivity
    have hsbig : 4 * c₀ / Real.exp 1 ^ 2 ≤ Real.sqrt (1 / δ) := by
      have hinv : (4 * c₀ / Real.exp 1 ^ 2) ^ 2 ≤ 1 / δ := by
        have h1 : (4 * c₀ / Real.exp 1 ^ 2) ^ 2 = 16 * c₀ ^ 2 / Real.exp 1 ^ 4 := by
          field_simp
          ring
        have h2 : 16 * c₀ ^ 2 / Real.exp 1 ^ 4 ≤ 1 / δ := by
          rw [div_le_div_iff₀ (by positivity) hδ0]
          have h3 := hδs
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 16 * c₀ ^ 2)] at h3
          nlinarith [h3]
        rw [h1]
        exact h2
      have h4 : Real.sqrt ((4 * c₀ / Real.exp 1 ^ 2) ^ 2) = 4 * c₀ / Real.exp 1 ^ 2 :=
        Real.sqrt_sq (by positivity)
      calc 4 * c₀ / Real.exp 1 ^ 2 = Real.sqrt ((4 * c₀ / Real.exp 1 ^ 2) ^ 2) := h4.symm
        _ ≤ Real.sqrt (1 / δ) := Real.sqrt_le_sqrt hinv
    have hkill : 4 * c₀ * Real.sqrt (1 / δ) ≤ Real.exp 1 ^ 2 / δ := by
      have h2 : (Real.exp 1 ^ 2 * Real.sqrt (1 / δ)) * (4 * c₀ / Real.exp 1 ^ 2)
          ≤ (Real.exp 1 ^ 2 * Real.sqrt (1 / δ)) * Real.sqrt (1 / δ) :=
        mul_le_mul_of_nonneg_left hsbig (by positivity)
      have h3 : (Real.exp 1 ^ 2 * Real.sqrt (1 / δ)) * (4 * c₀ / Real.exp 1 ^ 2)
          = 4 * c₀ * Real.sqrt (1 / δ) := by
        field_simp
      have h4 : (Real.exp 1 ^ 2 * Real.sqrt (1 / δ)) * Real.sqrt (1 / δ)
          = Real.exp 1 ^ 2 * (1 / δ) := by
        rw [mul_assoc, ← pow_two, hssq]
      have h5 : Real.exp 1 ^ 2 * (1 / δ) = Real.exp 1 ^ 2 / δ := by ring
      linarith [h2, h3.le, h3.ge, h4.le, h4.ge, h5.le, h5.ge]
    have habs : Real.log (2 * c₀) ≤ |Real.log (2 * c₀)| := le_abs_self _
    have hstep : c₀ * psi d Mv ≤ c₀ * Real.log (Mv + 2) :=
      mul_le_mul_of_nonneg_left hpsile hc₀.le
    have hlog2 : c₀ * Real.log (2 * c₀ / δ)
        ≤ c₀ * |Real.log (2 * c₀)| + 2 * c₀ * Real.sqrt (1 / δ) := by
      rw [hsplit, mul_add]
      have e1 : c₀ * Real.log (2 * c₀) ≤ c₀ * |Real.log (2 * c₀)| :=
        mul_le_mul_of_nonneg_left habs hc₀.le
      have e2 : c₀ * Real.log (1 / δ) ≤ c₀ * (2 * Real.sqrt (1 / δ)) :=
        mul_le_mul_of_nonneg_left hsqrt hc₀.le
      linarith [e1, e2]
    have hfin : c₀ * psi d Mv - δ * Mv ≤ 2 + c₀ * |Real.log (2 * c₀)| := by
      linarith [hstep, hlogbound, hlog2, hkill, hdM, hδ0.le, hδ1, hc₀.le]
    have hCge : 2 + c₀ * |Real.log (2 * c₀)| ≤ C * P ^ ((2:ℝ) / d) := by
      have h1 : (2:ℝ) + c₀ * |Real.log (2 * c₀)| ≤ C := by
        rw [hCdef]
        nlinarith [hc₀]
      nlinarith [h1, hPrp, hC0]
    linarith

/-- **Step 3 of `prop:near-divisible`** (`parking.tex:2881-2896`).  For a uniformly bounded
family above dimension four the limit mean odometer is at most `C [log(e/δ)]^{2/d}`. -/
theorem exists_meanuLimit_psi_upper (hd5 : 5 ≤ d)
    (hGrowth : Parking.External.SandpileGrowth) (hStopping : Parking.External.Stopping)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K)
    {B : ℤ} (hsupp : ∀ δ' ∈ Set.Icc (0:ℝ) δ₀, ν δ' {k : ℤ | B < |k|} = 0) :
    ∃ C δ₂ : ℝ, 0 < C ∧ 0 < δ₂ ∧ δ₂ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0:ℝ) δ₂,
      Parking.meanuLimit (Parking.law d (ν δ))
        ≤ ENNReal.ofReal (C * Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d)) := by
  have hd : 1 ≤ d := by omega
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  obtain ⟨C1, hC1, hMH⟩ :=
    exists_meanHorizon_psi hd5 hGrowth hStopping hConc hGreen hfam' hsupp
  obtain ⟨C2, δ₂, hC2, hδ₂, hδ₂1, hopt⟩ := exists_psi_sub_le d hd5 hC1
  refine ⟨C2, min δ₀ δ₂, hC2, lt_min hδ₀ hδ₂, min_le_left _ _, ?_⟩
  intro δ hδ
  have hδpos : 0 < δ := hδ.1
  have hδ0 : δ ≤ δ₀ := le_trans hδ.2 (min_le_left _ _)
  have hδs : δ ≤ δ₂ := le_trans hδ.2 (min_le_right _ _)
  have hδicc : δ ∈ Set.Icc (0:ℝ) δ₀ := ⟨hδpos.le, hδ0⟩
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδicc
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d (ν δ)) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδicc).1
  have hintabs : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    (integrable_intCast_of_exp hθ (ν δ) hintexp).abs
  have hbound : ∀ n : ℕ, meanu (law d (ν δ)) n
      ≤ C2 * Real.log (Real.exp 1 / δ) ^ ((2:ℝ) / d) := by
    intro n
    have hσ : ∀ η : Site d → ℤ, LatticeProb.IsWalkStopping (optStop n η) := fun η =>
      isWalkStopping_zdOptimalStop hd _ n
    have hσn : ∀ (η : Site d → ℤ) X, optStop n η X ≤ n := fun η X => zdOptimalStop_le hd _ n X
    have hm : ∀ X, Measurable fun η : Site d → ℤ => optStop n η X := fun X =>
      measurable_optStop hd n X
    set A : (Site d → ℤ) → ℝ := fun η =>
      ∫ X, ((optStop n η X : ℕ) : ℝ) ∂(LatticeProb.siteWalkLaw d (0 : Site d)) with hA
    set Mσ : ℝ := ∫ η, A η ∂(LatticeProb.iidLaw d (ν δ)) with hMσ
    obtain ⟨hIr, hbd⟩ := hMH δ hδicc n (optStop n) hσ hσn hm Mσ rfl
    have hIA : Integrable A (LatticeProb.iidLaw d (ν δ)) := integrable_optStopAvg hd n (ν δ)
    have hmeanu : meanu (law d (ν δ)) n
        = (∫ η, rewardAvg δ (optStop n) η ∂(LatticeProb.iidLaw d (ν δ))) - δ * Mσ := by
      rw [meanu_eq_integral_u hd (ν δ) hintabs n]
      have hcongr : ∀ η : Site d → ℤ,
          u (fun y => ((η y : ℤ) : ℝ)) n 0 = rewardAvg δ (optStop n) η - δ * A η :=
        fun η => u_eq_rewardAvg_sub hd δ n η
      rw [integral_congr_ae (Filter.Eventually.of_forall hcongr),
        integral_sub hIr (hIA.const_mul δ), integral_const_mul]
    have hM0 : 0 ≤ Mσ := by
      rw [hMσ]
      exact integral_nonneg fun η => integral_nonneg fun X => Nat.cast_nonneg _
    have hfin := hopt δ hδpos hδs Mσ hM0
    rw [hmeanu]
    linarith
  rw [Parking.meanuLimit]
  exact iSup_le fun n => ENNReal.ofReal_le_ofReal (hbound n)
