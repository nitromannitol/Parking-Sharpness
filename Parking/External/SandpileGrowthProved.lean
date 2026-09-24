/-
The flagship growth input for Parking, discharged from the sealed growth
theorems in `Divisible-Sandpile-Percolation`.

The sandpile package proves the random-walk inputs `VarianceScale` and
`GreenBoundsHigh` in its `*Proved.lean` files; this module uses those proofs
directly.  The remaining inputs are carried explicitly because that package
still states them as external hypotheses: `Sandpile.External.LocalCLT`,
`Sandpile.External.ContinuumStoppingStability.{0}`, and the family of finite-
horizon Brownian optimal-stopping hypotheses
`∀ (ΩB : Type) [MeasurableSpace ΩB],
Sandpile.External.ContinuumOptimalStopping ΩB`.  No proof of any of these
three cited inputs is introduced here.

The high-dimensional all-time upper bounds use the package's sealed crude
and refined increment results.  The lower bounds supplied by
`Sandpile.Frozen.high_first_order` are eventual; the elementary extension to
all `n ≥ 2` is proved below using monotonicity and positivity at time one.
-/
import Parking.Support.SandpileBridge
import Sandpile.External.VarianceScaleProved
import Sandpile.External.GreenBoundsHighProved
import Sandpile.Frozen.MeanGrowthLow
import Sandpile.Frozen.MeanGrowthFour
import Sandpile.Frozen.HighFirstOrder
import Sandpile.Support.CrudeIncrement
import Sandpile.Frozen.DGT4HeightUpperTail

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal


private theorem all_bounds_of_eventual
    (M : ℕ → ℝ) (hmono : Monotone M) (hM1 : 0 < M 1)
    (p : ℝ) (hp : 0 < p)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ p ≤ M n)
    (hupper : ∀ᶠ n : ℕ in atTop, M n ≤ C * (n : ℝ) ^ p) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧ ∀ n : ℕ, 2 ≤ n →
      c' * (n : ℝ) ^ p ≤ M n ∧ M n ≤ C' * (n : ℝ) ^ p := by
  obtain ⟨N₁, hN₁⟩ := hlower.exists_forall_of_atTop
  obtain ⟨N₂, hN₂⟩ := hupper.exists_forall_of_atTop
  let T : ℕ := max (max N₁ N₂) 2
  have hT2 : 2 ≤ T := le_max_right _ _
  have hT1 : 1 ≤ T := le_trans (by omega) hT2
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 0 < Real.log (T : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hpowT : 0 < (T : ℝ) ^ p := Real.rpow_pos_of_pos hTpos p
  have hpow2 : 0 < (2 : ℝ) ^ p := by positivity
  have hMnonneg : 0 ≤ M T :=
    le_trans (le_of_lt hM1) (hmono (le_trans (by omega) hT1))
  let c' : ℝ := min c (M 1 / (T : ℝ) ^ p)
  let C' : ℝ := max C (M T / (2 : ℝ) ^ p)
  have hc' : 0 < c' := by
    apply lt_min hc
    exact div_pos hM1 hpowT
  have hC' : 0 < C' := by
    apply lt_of_lt_of_le hC (le_max_left _ _)
  refine ⟨c', C', hc', hC', ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpow_n : 0 ≤ (n : ℝ) ^ p := (Real.rpow_nonneg hnpos.le _)
  by_cases hlarge : T ≤ n
  · constructor
    · exact le_trans
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow_n)
        (hN₁ n (by
          have hN1T : N₁ ≤ T := by dsimp [T]; omega
          exact hN1T.trans hlarge))
    · exact le_trans
        (hN₂ n (by
          have hN2T : N₂ ≤ T := by dsimp [T]; omega
          exact hN2T.trans hlarge))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow_n)
  · have hnT : n ≤ T := by omega
    have hpow_le : (n : ℝ) ^ p ≤ (T : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnT) hp.le
    have hpow_n_pos : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos hnpos p
    have hM1n : M 1 ≤ M n := hmono (by omega)
    have hMT : M n ≤ M T := hmono hnT
    constructor
    · calc
        c' * (n : ℝ) ^ p ≤ (M 1 / (T : ℝ) ^ p) * (n : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow_n
        _ ≤ (M 1 / (T : ℝ) ^ p) * (T : ℝ) ^ p :=
          mul_le_mul_of_nonneg_left hpow_le (div_nonneg hM1.le hpowT.le)
        _ = M 1 := by field_simp
        _ ≤ M n := hM1n
    · calc
        M n ≤ M T := hMT
        _ ≤ (M T / (2 : ℝ) ^ p) * (n : ℝ) ^ p := by
          have hpow2n : (2 : ℝ) ^ p ≤ (n : ℝ) ^ p :=
            Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hn) hp.le
          have hcoef : 0 ≤ M T / (2 : ℝ) ^ p :=
            div_nonneg hMnonneg hpow2.le
          calc
            M T = (M T / (2 : ℝ) ^ p) * (2 : ℝ) ^ p := by field_simp
            _ ≤ (M T / (2 : ℝ) ^ p) * (n : ℝ) ^ p :=
              mul_le_mul_of_nonneg_left hpow2n hcoef
        _ ≤ C' * (n : ℝ) ^ p :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow_n

private theorem scaled_limit_eventual_bounds
    (M : ℕ → ℝ) (p L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-p) * M n)
      atTop (𝓝 L)) :
    (∀ᶠ n : ℕ in atTop, (L / 2) * (n : ℝ) ^ p ≤ M n) ∧
      (∀ᶠ n : ℕ in atTop, M n ≤ (2 * L) * (n : ℝ) ^ p) := by
  have hmem : Set.Ioo (L / 2) (2 * L) ∈ 𝓝 L :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hev : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-p) * M n ∈ Set.Ioo (L / 2) (2 * L) := hlim.eventually hmem
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  constructor
  · filter_upwards [hev, hlarge] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpow : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg hnpos.le _
    have hcancel : (n : ℝ) ^ p * ((n : ℝ) ^ (-p) * M n) = M n := by
      rw [← mul_assoc, ← Real.rpow_add hnpos]
      simp
    calc
      (L / 2) * (n : ℝ) ^ p = (n : ℝ) ^ p * (L / 2) := by ring
      _ ≤ (n : ℝ) ^ p * ((n : ℝ) ^ (-p) * M n) :=
        mul_le_mul_of_nonneg_left hn.1.le hpow
      _ = M n := hcancel
  · filter_upwards [hev, hlarge] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hpow : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg hnpos.le _
    have hcancel : (n : ℝ) ^ p * ((n : ℝ) ^ (-p) * M n) = M n := by
      rw [← mul_assoc, ← Real.rpow_add hnpos]
      simp
    calc
      M n = (n : ℝ) ^ p * ((n : ℝ) ^ (-p) * M n) := hcancel.symm
      _ ≤ (n : ℝ) ^ p * (2 * L) := mul_le_mul_of_nonneg_left hn.2.le hpow
      _ = (2 * L) * (n : ℝ) ^ p := by ring

private theorem all_lower_of_eventual
    (M : ℕ → ℝ) (hmono : Monotone M) (hM1 : 0 < M 1)
    (p : ℝ) (hp : 0 < p) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ p ≤ M n) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
      c' * (n : ℝ) ^ p ≤ M n := by
  obtain ⟨N, hN⟩ := hlower.exists_forall_of_atTop
  let T : ℕ := max N 2
  have hT2 : 2 ≤ T := le_max_right _ _
  have hT1 : 1 ≤ T := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hpowT : 0 < (T : ℝ) ^ p := Real.rpow_pos_of_pos hTpos p
  let c' : ℝ := min c (M 1 / (T : ℝ) ^ p)
  have hc' : 0 < c' := by
    apply lt_min hc
    exact div_pos hM1 hpowT
  refine ⟨c', hc', ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpow_n : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg hnpos.le _
  by_cases hlarge : T ≤ n
  · exact le_trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow_n)
      (hN n (le_trans (le_max_left _ _) hlarge))
  · have hnT : n ≤ T := by omega
    have hpow_le : (n : ℝ) ^ p ≤ (T : ℝ) ^ p :=
      Real.rpow_le_rpow hnpos.le (by exact_mod_cast hnT) hp.le
    have hM1n : M 1 ≤ M n := hmono (by omega)
    calc
      c' * (n : ℝ) ^ p ≤ (M 1 / (T : ℝ) ^ p) * (n : ℝ) ^ p :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hpow_n
      _ ≤ (M 1 / (T : ℝ) ^ p) * (T : ℝ) ^ p :=
        mul_le_mul_of_nonneg_left hpow_le (div_nonneg hM1.le hpowT.le)
      _ = M 1 := by field_simp
      _ ≤ M n := hM1n

private theorem all_lower_log_of_eventual
    (M : ℕ → ℝ) (hmono : Monotone M) (hM1 : 0 < M 1)
    (q : ℝ) (hq : 0 < q) (c : ℝ) (hc : 0 < c)
    (hlower : ∀ᶠ n : ℕ in atTop, c * (Real.log n) ^ q ≤ M n) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n : ℕ, 2 ≤ n →
      c' * (Real.log n) ^ q ≤ M n := by
  obtain ⟨N, hN⟩ := hlower.exists_forall_of_atTop
  let T : ℕ := max N 2
  have hT2 : 2 ≤ T := le_max_right _ _
  have hT1 : 1 ≤ T := by omega
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hlogT : 0 < Real.log (T : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < T))
  have hpowT : 0 < (Real.log (T : ℝ)) ^ q :=
    Real.rpow_pos_of_pos hlogT q
  let c' : ℝ := min c (M 1 / (Real.log (T : ℝ)) ^ q)
  have hc' : 0 < c' := by
    apply lt_min hc
    exact div_pos hM1 hpowT
  refine ⟨c', hc', ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      exact hn1)
  have hpow_n : 0 ≤ (Real.log (n : ℝ)) ^ q := Real.rpow_nonneg hlogn _
  by_cases hlarge : T ≤ n
  · exact le_trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hpow_n)
      (hN n (by
        have hNT : N ≤ T := by dsimp [T]; omega
        exact hNT.trans hlarge))
  · have hnT : n ≤ T := by omega
    have hlog_le : Real.log (n : ℝ) ≤ Real.log (T : ℝ) :=
      Real.log_le_log hnpos (by exact_mod_cast hnT)
    have hpow_le : (Real.log (n : ℝ)) ^ q ≤ (Real.log (T : ℝ)) ^ q :=
      Real.rpow_le_rpow hlogn hlog_le hq.le
    have hM1n : M 1 ≤ M n := hmono (by omega)
    calc
      c' * (Real.log (n : ℝ)) ^ q ≤
          (M 1 / (Real.log (T : ℝ)) ^ q) * (Real.log (n : ℝ)) ^ q :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hpow_n
      _ ≤ (M 1 / (Real.log (T : ℝ)) ^ q) * (Real.log (T : ℝ)) ^ q :=
        mul_le_mul_of_nonneg_left hpow_le (div_nonneg hM1.le hpowT.le)
      _ = M 1 := by field_simp
      _ ≤ M n := hM1n

private theorem meanOdometer_one_pos (d : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hd : 1 ≤ d) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (_hvar' : evariance id ν < ⊤)
    (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    0 < Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) 1 := by
  have hint : Integrable (id : ℝ → ℝ) ν :=
    Sandpile.integrable_id_of_exp_moment ν θ hθ hexp
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    exact hint.abs.mono' (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  have hIoi : 0 < ν (Set.Ioi (0 : ℝ)) := by
    by_contra h
    have hz : ν (Set.Ioi (0 : ℝ)) = 0 := by
      exact le_antisymm (not_lt.mp h) bot_le
    have hle : ∀ᵐ z ∂ν, z ≤ 0 := by
      apply MeasureTheory.ae_iff.mpr
      simpa [Set.Ioi, not_le] using hz
    have hneg : ∀ᵐ z ∂ν, 0 ≤ -z := hle.mono fun z hz => by linarith
    have hnegzero : ∫ z, -z ∂ν = 0 := by rw [integral_neg, hmean]; simp
    have hzero : (id : ℝ → ℝ) =ᵐ[ν] 0 := by
      have h := (integral_eq_zero_iff_of_nonneg_ae hneg hint.neg).1 hnegzero
      filter_upwards [h] with z hz
      change -z = 0 at hz
      change z = 0
      linarith
    have hvarzero : evariance (id : ℝ → ℝ) ν = 0 :=
      (evariance_eq_zero_iff measurable_id.aemeasurable).2 (by
        change id =ᵐ[ν] (fun _ => (∫ z, z ∂ν))
        rw [hmean]
        exact hzero)
    exact (ne_of_gt hvar) hvarzero
  have hmax : 0 < ∫ z, max z 0 ∂ν := by
    apply (integral_pos_iff_support_of_nonneg (fun z => le_max_right z 0) hpos).2
    simpa [Function.support, Set.Ioi, not_le] using hIoi
  rw [Sandpile.meanOdometer_eq d ν hd 1]
  have hmean1 : (∫ ζ : Sandpile.Site d → ℝ,
      Sandpile.odometerOf ζ 1 0 ∂(LatticeProb.iidLaw d ν)) =
      ∫ ζ : Sandpile.Site d → ℝ, max (ζ 0) 0 ∂(LatticeProb.iidLaw d ν) := by
    apply integral_congr_ae
    filter_upwards [] with ζ
    simp [Sandpile.odometerOf, Sandpile.avg, LatticeProb.walkOp,
      LatticeProb.nbrSum, max_comm]
  rw [hmean1]
  rw [LatticeProb.iidLaw,
    LatticeProb.integral_eval (fun _ : Sandpile.Site d => ν) 0 (fun z : ℝ => max z 0)
      (by fun_prop)]
  simpa [Sandpile.odometerOf, Sandpile.avg] using hmax

private theorem upper_log_of_crude
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν)
    (hvar' : evariance id ν < ⊤) (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n ≤ C * Real.log (n + 1) := by
  haveI := hprob
  obtain ⟨K, hK, hcrude⟩ := Sandpile.exists_crude_log_upper
    Sandpile.External.greenBoundsHigh hd ν hprob hmean hvar hvar' θ
    (∫ z, Real.exp (θ * |z|) ∂ν) hθ hexp le_rfl
  refine ⟨2 * K, by positivity, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : Real.log ((n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsquare : (n : ℝ) + 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [sq_nonneg (n : ℝ)]
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 2) hsquare
    rw [Real.log_pow] at h
    exact h
  rw [Sandpile.meanOdometer_eq d ν (le_trans (by norm_num) hd) n]
  calc
    (∫ ζ, Sandpile.odometerOf ζ n 0 ∂(LatticeProb.iidLaw d ν)) ≤
        K * Real.log ((n : ℝ) + 2) := hcrude n
    _ ≤ K * (2 * Real.log ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hlog hK.le
    _ = (2 * K) * Real.log ((n : ℝ) + 1) := by ring

private theorem upper_power_of_bounded
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν)
    (hvar' : evariance id ν < ⊤) (θ : ℝ) (hθ : 0 < θ)
    (hexp : Integrable (fun z => Real.exp (θ * |z|)) ν)
    (hbounded : ∃ b : ℝ, ∀ᵐ z ∂ν, b ≤ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n ≤
        C * (Real.log n) ^ ((2 : ℝ) / d) := by
  haveI := hprob
  obtain ⟨b, hb⟩ := hbounded
  let γ : ℝ := (d : ℝ) / 2 + 1
  let s₀ : ℝ := max 1 (-b + 1)
  have hγ : 1 ≤ γ := by
    dsimp [γ]
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (by omega : 2 ≤ d)
    linarith
  have hγd : γ ≠ (d : ℝ) / 2 := by dsimp [γ]; linarith
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (1 * Real.exp (-(1 * s ^ γ))) := by
    intro s hs
    have hsb : -s < b := by
      have : 1 ≤ s := le_trans (le_max_left _ _) hs
      have : -b + 1 ≤ s := le_trans (le_max_right _ _) hs
      linarith
    have hnull : ν (Set.Iio b) = 0 := by
      have h := MeasureTheory.ae_iff.mp hb
      simpa [Set.Iio, not_le] using h
    have hsub : Set.Iic (-s) ⊆ Set.Iio b := by
      intro z hz
      exact lt_of_le_of_lt hz hsb
    rw [measure_mono_null hsub hnull]
    exact bot_le
  obtain ⟨C, hC, hupper⟩ := Sandpile.Frozen.dgt4_height_upper_tail
    Sandpile.External.greenBoundsHigh d hd ν hprob hmean hvar hvar' θ
    (∫ z, Real.exp (θ * |z|) ∂ν) hθ hexp le_rfl γ hγ hγd 1 1 s₀
    one_pos one_pos hs₀ htail
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hmin : min γ ((d : ℝ) / 2) = (d : ℝ) / 2 := by
    apply min_eq_right
    dsimp [γ]
    linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num) hd)
  have hexp : (1 : ℝ) / min γ ((d : ℝ) / 2) = (2 : ℝ) / d := by
    rw [hmin]
    field_simp
  have hupper' : ∀ t : ℕ, 2 ≤ t →
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ≤
        C * (Real.log t) ^ ((2 : ℝ) / d) := by
    intro t ht
    have h := hupper t ht
    rw [hexp] at h
    exact h
  exact hupper' n hn

private theorem sandpileGrowth_proof
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB],
      Sandpile.External.ContinuumOptimalStopping ΩB) :
    Parking.External.SandpileGrowth := by
  intro d hd ν hprob hmean hvar hvar' hexp
  haveI := hprob
  obtain ⟨θ, hθ, hexpint⟩ := hexp
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    exact (Sandpile.integrable_id_of_exp_moment ν θ hθ hexpint).abs.mono'
      (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  have hmono : Monotone (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) := by
    intro m n hmn
    exact Sandpile.meanOdometer_mono hd ν hpos hmn
  have hone : 0 < Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) 1 :=
    meanOdometer_one_pos d ν hd hmean hvar hvar' θ hθ hexpint
  constructor
  · intro hd3
    obtain ⟨L, hL, hlim⟩ := Sandpile.Frozen.mean_growth_le_three hLocalCLT hStab
      Sandpile.External.varianceScale hOS d hd hd3 ν hprob hmean hvar hvar'
      θ hθ hexpint
    let p : ℝ := (4 - (d : ℝ)) / 4
    have hp : 0 < p := by
      dsimp [p]
      have hd3' : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
      linarith
    have hlim' : Tendsto (fun n : ℕ => (n : ℝ) ^ (-p) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) atTop (𝓝 L) := by
      simpa [p] using hlim
    obtain ⟨hlowerEv, hupperEv⟩ := scaled_limit_eventual_bounds
      (fun n => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) p L hL hlim'
    obtain ⟨c, C, hc, hC, hb⟩ := all_bounds_of_eventual
      (fun n => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) hmono hone p hp
      (L / 2) (2 * L) (by linarith) (by linarith) hlowerEv hupperEv
    refine ⟨c, C, hc, hC, ?_⟩
    intro n hn
    rw [Parking.meanSandpileReal_eq_sandpileMean d ν hd n]
    exact hb n hn
  · constructor
    · intro hd4
      subst d
      obtain ⟨c, C, hc, hC, hb⟩ := Sandpile.Frozen.mean_growth_four ν hprob hmean hvar hvar'
        θ hθ hexpint
      refine ⟨c, C, hc, hC, ?_⟩
      intro n hn
      simpa only [Parking.meanSandpileReal_eq_sandpileMean 4 ν (by norm_num)] using hb n hn
    · constructor
      · intro hd5
        obtain ⟨-, ⟨clow, hclow, heventlow⟩⟩ :=
          Sandpile.Frozen.high_first_order Sandpile.External.greenBoundsHigh d hd5 ν hprob
            hmean hvar hvar' θ hθ hexpint
        obtain ⟨clow', hclow', hlowall⟩ := all_lower_log_of_eventual
          (fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)
          hmono hone ((2 : ℝ) / d) (by positivity) clow hclow heventlow
        obtain ⟨C, hC, hupper⟩ := upper_log_of_crude d hd5 ν hprob hmean hvar hvar'
          θ hθ hexpint
        refine ⟨clow', 2 * C, hclow', by positivity, ?_⟩
        intro n hn
        rw [Parking.meanSandpileReal_eq_sandpileMean d ν hd n]
        exact ⟨hlowall n hn, by
          have hu := hupper n hn
          have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
            nlinarith
          have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hn1
          nlinarith⟩
      · constructor
        · intro hd5 hbounded
          obtain ⟨-, ⟨clow, hclow, heventlow⟩⟩ :=
            Sandpile.Frozen.high_first_order Sandpile.External.greenBoundsHigh d hd5 ν hprob
              hmean hvar hvar' θ hθ hexpint
          obtain ⟨clow', hclow', hlowall⟩ := all_lower_log_of_eventual
            (fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)
            hmono hone ((2 : ℝ) / d) (by positivity) clow hclow heventlow
          obtain ⟨C, hC, hupper⟩ := upper_power_of_bounded d hd5 ν hprob hmean hvar hvar'
            θ hθ hexpint hbounded
          refine ⟨clow', C, hclow', hC, ?_⟩
          intro n hn
          rw [Parking.meanSandpileReal_eq_sandpileMean d ν hd n]
          exact ⟨hlowall n hn, hupper n hn⟩
        · intro hd3
          obtain ⟨L, hL, hlim⟩ := Sandpile.Frozen.mean_growth_le_three hLocalCLT hStab
            Sandpile.External.varianceScale hOS d hd hd3 ν hprob hmean hvar hvar'
            θ hθ hexpint
          refine ⟨L, hL, ?_⟩
          simpa only [Parking.meanSandpileReal_eq_sandpileMean d ν hd] using hlim

-- FROZEN-STATEMENT-BEGIN
theorem Parking.External.sandpileGrowth
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB],
      Sandpile.External.ContinuumOptimalStopping ΩB) :
    Parking.External.SandpileGrowth
-- FROZEN-STATEMENT-END
:= by
  exact sandpileGrowth_proof hLocalCLT hStab hOS

