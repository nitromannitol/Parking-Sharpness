/-
Step 1 of `lem:mean-horizon` (`parking.tex:2775-2801`).

Step 1 is the moment bound `(E u_m(0;ξ_δ)^q)^{1/q} ≤ C_q φ_d(m)`, UNIFORMLY in
`δ`, and the source of that uniformity is `eq:near-convex`: the one-site law of
`ξ_δ(0)` is below a FIXED law in convex order, after which `thm:BP`,
`lem:u-concentration` and `eq:green-norms` are applied at that fixed law alone,
with constants that no longer see `δ`.

The fixed law is `refZeta θ δ₀ M`, the reference law of
`Parking/Support/ConvexOrder.lean` built from the two numbers the family
supplies: the rate `θ` of its exponential moment and the bound `M` on that
moment.  Only the product `e^{θδ₀}M` enters, so the same law serves every
`δ ∈ [0,δ₀]`.

The comparison is at every moment, not only the first: `ξ ↦ u_m(0;ξ)^r` is
convex but not Lipschitz, so `Parking/Support/UMoment.lean` writes the power as
an integral of its hinges, each of which IS convex, nondecreasing and
1-Lipschitz, and integrates the hinge comparison over the level.

The exponent is `q = 5`, which serves every dimension: the paper needs
`1 - 1/q > (4-d)/4` when `d ≤ 3`, and `1 - 1/5 = 4/5 > 3/4`.
-/
import Parking.Support.UConcReal
import Parking.Support.MeanPos
import Parking.Support.GreenPhi
import Parking.Support.XiLaw
import Parking.Support.UMoment
import Parking.Support.URealMoment
import Parking.External.SandpileGrowth
import Parking.External.GreenNorms

noncomputable section

namespace Parking

open MeasureTheory LatticeProb ProbabilityTheory

variable {d : ℕ}

theorem integrable_maxPow_of_exp (ζ : Measure ℝ) [IsProbabilityMeasure ζ] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) ζ) (k : ℕ) :
    Integrable (fun t : ℝ => max t 0 ^ k) ζ := by
  refine Integrable.mono' (integrable_abs_pow_of_exp_moment ζ hθ hexp k)
    ((measurable_id.max measurable_const).pow_const _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_max_right t 0) _)]
  exact pow_le_pow_left₀ (le_max_right t 0) (max_le (le_abs_self t) (abs_nonneg t)) _


theorem integrable_intCast_of_exp {θ : ℝ} (hθ : 0 < θ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    Integrable (fun k : ℤ => ((k : ℝ))) ν := by
  refine Integrable.mono' (hint.const_mul θ⁻¹)
    (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall fun k => ?_)
  rw [Real.norm_eq_abs]
  have h1 : θ * |(k : ℝ)| ≤ Real.exp (θ * |(k : ℝ)|) := by
    have := Real.add_one_le_exp (θ * |(k : ℝ)|)
    linarith
  rw [inv_mul_eq_div, le_div_iff₀ hθ]
  linarith [h1]

theorem one_le_integral_exp_abs {θ : ℝ} (hθ : 0 < θ) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    1 ≤ ∫ k, Real.exp (θ * |(k : ℝ)|) ∂ν := by
  have h := integral_mono (integrable_const (1:ℝ)) hint (fun k => ?_)
  · simpa using h
  · exact Real.one_le_exp (by positivity)

/-- The reference law of Step 1: the exponential-moment bound of the family, uniform
in the shift. -/
def refBound (θ δ₀ M : ℝ) : ℝ := Real.exp (θ * δ₀) * M

/-- The fixed symmetric reference law `ζ` of `eq:near-convex`, the same for every `δ`. -/
def refZeta (θ δ₀ M : ℝ) : Measure ℝ :=
  refLaw θ⁻¹ (2 * Real.log (refBound θ δ₀ M) / θ)

/-- **The coordinate replacement of Step 1.**  Every moment of the odometer of the
recentred scenery is below the same moment at the fixed reference law, for every
`δ ∈ [0, δ₀]`. -/
theorem integral_pow_u_xi_le (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {δ : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) δ₀) (k m : ℕ) :
    ∫ η, u (Parking.xi δ η) m 0 ^ (k + 2) ∂(LatticeProb.iidLaw d (ν δ))
      ≤ ∫ η, u η m 0 ^ (k + 2) ∂(LatticeProb.iidLaw d (refZeta θ δ₀ M)) := by
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  haveI hpν : IsProbabilityMeasure (ν δ) := hprob δ hδ
  have hintexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) (ν δ) := (hexp δ hδ).1
  have hMle : ∫ k, Real.exp (θ * |(k : ℝ)|) ∂(ν δ) ≤ M := (hexp δ hδ).2
  have hM1 : 1 ≤ M := le_trans (one_le_integral_exp_abs hθ (ν δ) hintexp) hMle
  have hδ0 : 0 ≤ δ := hδ.1
  have hδd : δ ≤ δ₀ := hδ.2
  set A : ℝ := refBound θ δ₀ M with hA
  have hA1 : 1 ≤ A := by
    rw [hA, refBound]
    have h1 : (1:ℝ) ≤ Real.exp (θ * δ₀) := Real.one_le_exp (by positivity)
    nlinarith
  set μ : Measure ℝ := shiftLaw δ (ν δ) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hintid : Integrable (fun k : ℤ => ((k : ℝ))) (ν δ) :=
    integrable_intCast_of_exp hθ (ν δ) hintexp
  have hμmean : ∫ z, z ∂μ = 0 := by
    rw [hμ, integral_shiftLaw_id δ (ν δ) hintid, hmeanν δ hδ]
    ring
  have hμid : Integrable (id : ℝ → ℝ) μ := by
    rw [hμ]; exact integrable_id_shiftLaw δ (ν δ) hintid
  have hμexp : Integrable (fun z : ℝ => Real.exp (θ * |z|)) μ := by
    rw [hμ]; exact integrable_exp_abs_shiftLaw θ δ hθ.le (ν δ) hintexp
  have hμA : ∫ z, Real.exp (θ * |z|) ∂μ ≤ A := by
    have h := integral_exp_abs_shiftLaw_le θ δ M hθ.le (ν δ) hintexp hMle
    rw [abs_of_nonneg hδ0] at h
    refine le_trans h ?_
    rw [hA, refBound]
    have h1 : Real.exp (θ * δ) ≤ Real.exp (θ * δ₀) :=
      Real.exp_le_exp.mpr (by nlinarith)
    nlinarith [hM1]
  have hb : (0:ℝ) < θ⁻¹ := inv_pos.mpr hθ
  have hc : (0:ℝ) ≤ 2 * Real.log A / θ := by
    have : 0 ≤ Real.log A := Real.log_nonneg hA1
    positivity
  have hζid : Integrable (id : ℝ → ℝ) (refZeta θ δ₀ M) := by
    rw [refZeta, ← hA]
    exact integrable_refLaw_id _ _
  have hcomp : ∀ (f : ℝ → ℝ) (Kf : NNReal), ConvexOn ℝ Set.univ f → LipschitzWith Kf f →
      ∫ x, f x ∂μ ≤ ∫ x, f x ∂(refZeta θ δ₀ M) := by
    intro f Kf hf hfL
    rw [refZeta, ← hA]
    exact convex_integral_le_refLaw hθ hA1 hμexp hμA hμmean hf hfL
  haveI hpζ : IsProbabilityMeasure (refZeta θ δ₀ M) := by rw [refZeta]; infer_instance
  have hIζ : Integrable (fun η : Site d → ℝ => u η m 0 ^ (k + 2))
      (LatticeProb.iidLaw d (refZeta θ δ₀ M)) := by
    have hexpζ : Integrable (fun z : ℝ => Real.exp ((θ/2) * |z|)) (refZeta θ δ₀ M) := by
      rw [refZeta, ← hA]
      refine integrable_exp_abs_refLaw hb hc ?_
      rw [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hθ)]
      norm_num
    have hmax := integrable_maxPow_of_exp (refZeta θ δ₀ M) (by positivity : (0:ℝ) < θ/2)
      hexpζ (k + 2)
    exact integrable_u_pow_iid hd _ (k + 2) hmax m 0
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



theorem exists_mean_le_phi (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (hmean : ∫ z, z ∂ζ = 0) (hv0 : 0 < evariance id ζ) (hvT : evariance id ζ < ⊤)
    (hexp : ∃ θ : ℝ, 0 < θ ∧ Integrable (fun z : ℝ => Real.exp (θ * |z|)) ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      Parking.External.meanSandpileReal d ζ m ≤ C * phi d m := by
  obtain ⟨h3, h4, h5, -, -⟩ := hGrowth d hd ζ inferInstance hmean hv0 hvT hexp
  by_cases hd3 : d ≤ 3
  · obtain ⟨c, C, hc, hC, h⟩ := h3 hd3
    refine ⟨C, hC, fun m hm => ?_⟩
    have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    have hrate : (m:ℝ) ^ ((4 - (d:ℝ)) / 4) ≤ phi d m := by
      rw [phi, if_pos hd3]
      exact Real.rpow_le_rpow hm0 (by linarith) (by
        have : (d:ℝ) ≤ 3 := by exact_mod_cast hd3
        linarith)
    exact le_trans (h m hm).2 (by nlinarith [hrate, (h m hm).2])
  by_cases hd4 : d = 4
  · obtain ⟨c, C, hc, hC, h⟩ := h4 hd4
    refine ⟨C, hC, fun m hm => ?_⟩
    have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hrate : Real.log (m:ℝ) ≤ phi d m := by
      rw [phi, if_neg (by omega : ¬ d ≤ 3)]
      exact Real.log_le_log (by linarith) (by linarith)
    exact le_trans (h m hm).2 (by nlinarith [hrate])
  · have hd5 : 5 ≤ d := by omega
    obtain ⟨c, C, hc, hC, h⟩ := h5 hd5
    refine ⟨C, hC, fun m hm => ?_⟩
    have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hrate : Real.log ((m:ℝ) + 1) ≤ phi d m := by
      rw [phi, if_neg (by omega : ¬ d ≤ 3)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hle := (h m hm).2
    have : Real.log ((m : ℕ) + 1 : ℝ) = Real.log ((m:ℝ) + 1) := by norm_num
    rw [this] at hle
    nlinarith [hrate, Real.log_nonneg (by linarith : (1:ℝ) ≤ (m:ℝ) + 1)]


theorem log_two_le_phi (d : ℕ) (m : ℕ) : Real.log 2 ≤ phi d m := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [phi]
  split_ifs with h
  · have : (1:ℝ) ≤ ((m:ℝ) + 1) ^ ((4 - (d:ℝ)) / 4) := by
      refine Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) m; linarith) ?_
      have : (d:ℝ) ≤ 3 := by exact_mod_cast h
      linarith
    linarith
  · have h2 : (2:ℝ) ≤ (m:ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    exact Real.log_le_log (by norm_num) h2

/-- **Step 1 of `lem:mean-horizon` at the reference law.**  At a mean-zero law with a
finite exponential moment and a positive finite variance, the fifth moment norm of the
odometer is at most a constant times the scale `φ_d`.  `thm:BP` bounds the mean and
`lem:u-concentration` with `eq:green-norms` bounds the deviation, and both rates are
below `φ_d` (`Parking/Support/GreenPhi.lean`). -/
theorem exists_zeta_moment (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    (hmean : ∫ z, z ∂ζ = 0) (hv0 : 0 < evariance id ζ) (hvT : evariance id ζ < ⊤)
    {θ' : ℝ} (hθ' : 0 < θ') (hexp' : Integrable (fun z : ℝ => Real.exp (θ' * |z|)) ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      (∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d ζ)) ^ ((1:ℝ)/5) ≤ C * phi d m := by
  classical
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ζ) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ζ))
  obtain ⟨C0, hC0, hmeanle⟩ :=
    exists_mean_le_phi (d := d) hd hGrowth ζ hmean hv0 hvT ⟨θ', hθ', hexp'⟩
  obtain ⟨C1, hC1, hnorm⟩ := exists_uNormReal_le (d := d) hd hConc ζ hθ' hexp'
  obtain ⟨⟨c2, C2, hc2, hC2, hg2⟩, ⟨c3, C3, hc3, hC3, hg3⟩⟩ := hGreen d hd
  obtain ⟨C4, hC4, hrate⟩ := exists_green_phi d hd
  have hmaxpow : Integrable (fun t : ℝ => max t 0 ^ (⌈(5:ℝ)⌉₊)) ζ :=
    integrable_maxPow_of_exp ζ hθ' hexp' _
  have hI : ∀ m : ℕ, Integrable (fun η : Site d → ℝ => |u η m 0| ^ (5:ℝ))
      (LatticeProb.iidLaw d ζ) :=
    fun m => integrable_u_rpow_iid hd ζ (by norm_num) hmaxpow m 0
  set Z : ℕ → ℝ := fun m => ∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d ζ) with hZ
  have hZ0 : ∀ m, 0 ≤ Z m := fun m =>
    integral_nonneg fun η => Real.rpow_nonneg (abs_nonneg _) _
  have hmain : ∀ m : ℕ, 2 ≤ m → Z m ^ ((1:ℝ)/5)
      ≤ (C0 + C1 * C4 * (Real.sqrt 5 * C2 + 5 * C3)) * phi d m := by
    intro m hm
    have hm1 : 1 ≤ m := by omega
    have h1 := hnorm m hm1 5 (by norm_num)
    have h2 := hmeanle m hm
    have h3 := (hg2 m hm).2
    have h4 := (hg3 m hm).2
    have h5 := (hrate m hm).1
    have h6 := (hrate m hm).2
    have hphi0 : 0 ≤ phi d m := le_trans (le_of_lt (Real.log_pos (by norm_num))) (log_two_le_phi d m)
    have hs5 : (0:ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hl2 : l2Norm (green d m) ≤ C2 * (C4 * phi d m) := by nlinarith [hC2, h3, h5]
    have hmx : greenMax d m ≤ C3 * (C4 * phi d m) := by nlinarith [hC3, h4, h6]
    have hl20 : 0 ≤ l2Norm (green d m) := Real.sqrt_nonneg _
    have hmx0 : (0 : ℝ) ≤ greenMax d m := Real.iSup_nonneg fun x => green_nonneg m x
    calc Z m ^ ((1:ℝ)/5) ≤ Parking.External.meanSandpileReal d ζ m
            + C1 * (Real.sqrt 5 * l2Norm (green d m) + 5 * greenMax d m) := h1
      _ ≤ (C0 + C1 * C4 * (Real.sqrt 5 * C2 + 5 * C3)) * phi d m := by
            have e1 : Real.sqrt 5 * l2Norm (green d m) ≤ Real.sqrt 5 * (C2 * (C4 * phi d m)) :=
              mul_le_mul_of_nonneg_left hl2 hs5
            have e2 : (5:ℝ) * greenMax d m ≤ 5 * (C3 * (C4 * phi d m)) := by linarith
            have e3 : C1 * (Real.sqrt 5 * l2Norm (green d m) + 5 * greenMax d m)
                ≤ C1 * (Real.sqrt 5 * (C2 * (C4 * phi d m)) + 5 * (C3 * (C4 * phi d m))) :=
              mul_le_mul_of_nonneg_left (by linarith) hC1.le
            nlinarith [e3, h2]
  set Cm : ℝ := C0 + C1 * C4 * (Real.sqrt 5 * C2 + 5 * C3) with hCm
  have hCm0 : 0 < Cm := by
    have : 0 ≤ C1 * C4 * (Real.sqrt 5 * C2 + 5 * C3) := by positivity
    linarith
  have hmono : ∀ m : ℕ, m ≤ 2 → Z m ≤ Z 2 := by
    intro m hm
    refine integral_mono (hI m) (hI 2) fun η => ?_
    have hle : u η m 0 ≤ u η 2 0 := u_monotone_time hd η 0 hm
    rw [abs_of_nonneg (u_nonneg η m 0), abs_of_nonneg (u_nonneg η 2 0)]
    exact Real.rpow_le_rpow (u_nonneg η m 0) hle (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max Cm (Cm * phi d 2 / Real.log 2), lt_of_lt_of_le hCm0 (le_max_left _ _), fun m => ?_⟩
  have hphi0 : 0 ≤ phi d m := le_trans hlog2pos.le (log_two_le_phi d m)
  by_cases hm : 2 ≤ m
  · refine le_trans (hmain m hm) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hphi0
  · have hm2 : m ≤ 2 := by omega
    have h1 : Z m ^ ((1:ℝ)/5) ≤ Z 2 ^ ((1:ℝ)/5) :=
      Real.rpow_le_rpow (hZ0 m) (hmono m hm2) (by norm_num)
    have h2 : Z 2 ^ ((1:ℝ)/5) ≤ Cm * phi d 2 := hmain 2 le_rfl
    have h3 : Real.log 2 ≤ phi d m := log_two_le_phi d m
    have h4 : 0 ≤ Cm * phi d 2 := by
      have : 0 ≤ phi d 2 := le_trans hlog2pos.le (log_two_le_phi d 2)
      positivity
    have h5 : Cm * phi d 2 ≤ (Cm * phi d 2 / Real.log 2) * phi d m := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
      nlinarith [h3, h4]
    have h6 : (Cm * phi d 2 / Real.log 2) * phi d m
        ≤ max Cm (Cm * phi d 2 / Real.log 2) * phi d m :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hphi0
    linarith


/-- **Step 1 of `lem:mean-horizon`** (`parking.tex:2775-2801`), at the fifth moment.

The paper asks for `q > 1` with `1 - 1/q > (4-d)/4` when `d ≤ 3`, and any fixed `q > 1`
when `d ≥ 4`; `q = 5` serves every dimension, since `1 - 1/5 = 4/5 > 3/4 ≥ (4-d)/4`.

The bound is UNIFORM in `δ`: the only inputs are the mean `-δ` of the family and its
exponential moment `M`, and the reference law `refZeta θ δ₀ M` built from them does not
depend on `δ`, so `thm:BP`, `lem:u-concentration` and `eq:green-norms` are applied once,
at that law alone. -/
theorem exists_step1 (hd : 1 ≤ d) (hGrowth : Parking.External.SandpileGrowth)
    (hConc : Parking.External.UConcentration) (hGreen : Parking.External.GreenNorms)
    {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ} (hfam : NearFamily δ₀ ν θ M K) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Icc (0:ℝ) δ₀, ∀ m : ℕ,
      (∫ η, u (Parking.xi δ η) m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (ν δ))) ^ ((1:ℝ)/5)
        ≤ C * phi d m := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmeanν, -, hexp, -⟩ := hfam
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI hp0 : IsProbabilityMeasure (ν 0) := hprob 0 h0mem
  have hM1 : 1 ≤ M :=
    le_trans (one_le_integral_exp_abs hθ (ν 0) (hexp 0 h0mem).1) (hexp 0 h0mem).2
  have hA1 : 1 ≤ refBound θ δ₀ M := by
    rw [refBound]
    have h1 : (1:ℝ) ≤ Real.exp (θ * δ₀) := Real.one_le_exp (by positivity)
    nlinarith
  have hb : (0:ℝ) < θ⁻¹ := inv_pos.mpr hθ
  have hc : (0:ℝ) ≤ 2 * Real.log (refBound θ δ₀ M) / θ := by
    have : 0 ≤ Real.log (refBound θ δ₀ M) := Real.log_nonneg hA1
    positivity
  haveI hpζ : IsProbabilityMeasure (refZeta θ δ₀ M) := by rw [refZeta]; infer_instance
  have hζmean : ∫ z, z ∂(refZeta θ δ₀ M) = 0 := by rw [refZeta]; exact integral_refLaw_id _ _
  have hζv0 : 0 < evariance (id : ℝ → ℝ) (refZeta θ δ₀ M) := by
    rw [refZeta]; exact evariance_refLaw_pos hb hc
  have hζvT : evariance (id : ℝ → ℝ) (refZeta θ δ₀ M) < ⊤ := by
    rw [refZeta]; exact evariance_refLaw_lt_top _ _
  have hζexp : Integrable (fun z : ℝ => Real.exp ((θ/2) * |z|)) (refZeta θ δ₀ M) := by
    rw [refZeta]
    refine integrable_exp_abs_refLaw hb hc ?_
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hθ)]
    norm_num
  obtain ⟨C, hC, hCle⟩ := exists_zeta_moment (d := d) hd hGrowth hConc hGreen (refZeta θ δ₀ M)
    hζmean hζv0 hζvT (by positivity : (0:ℝ) < θ/2) hζexp
  refine ⟨C, hC, fun δ hδ m => ?_⟩
  have hconv : ∫ η, |u η m 0| ^ (5:ℝ) ∂(LatticeProb.iidLaw d (refZeta θ δ₀ M))
      = ∫ η, u η m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (refZeta θ δ₀ M)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show |u η m 0| ^ (5:ℝ) = u η m 0 ^ (5:ℕ)
    rw [abs_of_nonneg (u_nonneg η m 0), show (5:ℝ) = ((5:ℕ):ℝ) by norm_num,
      Real.rpow_natCast]
  have hcmp := integral_pow_u_xi_le (d := d) hd hfam' hδ 3 m
  have h5 : (3 : ℕ) + 2 = 5 := by norm_num
  rw [h5] at hcmp
  have hnn : (0:ℝ) ≤ ∫ η, u (Parking.xi δ η) m 0 ^ (5:ℕ) ∂(LatticeProb.iidLaw d (ν δ)) :=
    integral_nonneg fun η => pow_nonneg (u_nonneg _ m 0) _
  refine le_trans (Real.rpow_le_rpow hnn hcmp (by norm_num)) ?_
  rw [← hconv]
  exact hCle m

end Parking

end
