/-
The lower bound of `thm:near` in the limit mean, above dimension three
(`parking.tex:2896-2912`).

"Lemma 6.1 gives `S_t^0 ≥ c/(t+1)` for all large `t`.  Hence `S_t^δ ≥ c/(t+1)`
from that point up to `c/δ`, and summing proves
`E U_∞^δ(0) ≥ c log(e/δ)`."

The summation is carried out through the second conclusion of `lem:critical-density`,
`E U_n(0) ≥ c log n - C` at the critical law, which is the sum of `S_t^0` already
performed.  `eq:transport` turns both mean odometers into sums of survivor counts, so
the coupled comparison of `Parking/Support/NearDensity.lean` costs `n K δ` over a
horizon `n`.  The horizon `n = ⌈1/δ⌉` makes that loss at most `2K` while keeping
`log n ≥ log(e/δ) - 1`, so half of the critical constant survives once `log(e/δ)` is
large enough.
-/
import Parking.Support.NearDensity
import Parking.Support.NearTiltInterval
import Parking.Frozen.CriticalDensity

open MeasureTheory LatticeProb
open scoped ENNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The limit mean odometer dominates the mean at every horizon. -/
theorem ofReal_meanU_le_meanUlimit (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) :
    ENNReal.ofReal (Parking.meanU (Parking.law d ν) n)
      ≤ Parking.meanUlimit (Parking.law d ν) := by
  have hIU : Integrable (fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ)) (Parking.law d ν) :=
    integrable_U_law hd ν hint n 0
  have h2 : ENNReal.ofReal (Parking.meanU (Parking.law d ν) n)
      = ∫⁻ ω, ENNReal.ofReal ((Parking.U ω n 0 : ℕ) : ℝ) ∂(Parking.law d ν) := by
    rw [Parking.meanU]
    exact ofReal_integral_eq_lintegral_ofReal hIU
      (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)
  have h3 : ∀ ω : Data d, ENNReal.ofReal ((Parking.U ω n 0 : ℕ) : ℝ)
      ≤ ((Parking.Ulimit ω 0 : ℕ∞) : ℝ≥0∞) := by
    intro ω
    rw [ENNReal.ofReal_natCast, Parking.Ulimit, ENat.toENNReal_iSup]
    refine le_trans (le_of_eq ?_)
      (le_iSup (fun m : ℕ => ((((Parking.U ω m 0 : ℕ) : ℕ∞)) : ℝ≥0∞)) n)
    simp
  rw [h2]
  exact lintegral_mono h3

/-- The survivor count of the family at `δ` is below that of the critical member by
at most the mean coupling distance. -/
theorem S_ge_of_nearFamily (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) δ₀) (t : ℕ) :
    Parking.S (Parking.law d (ν 0)) t - K * δ ≤ Parking.S (Parking.law d (ν δ)) t := by
  obtain ⟨hδ₀, hθ, hprob, hmean, hnc, hexp, hcouple⟩ := hfam
  obtain ⟨pri, hpri, hf, hs, hKd⟩ := hcouple δ hδ
  have hδmem : δ ∈ Set.Icc (0 : ℝ) δ₀ := ⟨hδ.1.le, hδ.2⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI := hprob δ hδmem
  haveI := hprob 0 h0mem
  have hintd : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    integrable_abs_of_absMoment hθ (hexp δ hδmem).1
  have hint0 : Integrable (fun k : ℤ => |(k : ℝ)|) (ν 0) :=
    integrable_abs_of_absMoment hθ (hexp 0 h0mem).1
  have hmain := S_sub_couplingCost_le hd (ν δ) (ν 0) hintd hint0 pri hpri hf hs t
  linarith

/-- The mean odometer of the family at `δ` is below that of the critical member by at
most the horizon times the mean coupling distance. -/
theorem meanU_ge_of_nearFamily (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) δ₀) (n : ℕ) :
    Parking.meanU (Parking.law d (ν 0)) n - (n : ℝ) * (K * δ)
      ≤ Parking.meanU (Parking.law d (ν δ)) n := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmean, hnc, hexp, hcouple⟩ := hfam
  have hδmem : δ ∈ Set.Icc (0 : ℝ) δ₀ := ⟨hδ.1.le, hδ.2⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI := hprob δ hδmem
  haveI := hprob 0 h0mem
  have hintd : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    integrable_abs_of_absMoment hθ (hexp δ hδmem).1
  have hint0 : Integrable (fun k : ℤ => |(k : ℝ)|) (ν 0) :=
    integrable_abs_of_absMoment hθ (hexp 0 h0mem).1
  haveI hpd : IsProbabilityMeasure (LatticeProb.iidLaw d (ν δ)) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI hpc : IsProbabilityMeasure (LatticeProb.iidLaw d (ν 0)) := by
    unfold LatticeProb.iidLaw; infer_instance
  have hsumd : Parking.meanU (Parking.law d (ν δ)) n
      = ∑ s ∈ Finset.range n, Parking.S (Parking.law d (ν δ)) s :=
    meanU_eq_sum_S (μ := LatticeProb.iidLaw d (ν δ)) hd (fun v => iidLaw_map_shiftConf' (ν δ) v)
      (integrable_eval_iid (d := d) (ν δ) hintd 0) n
  have hsumc : Parking.meanU (Parking.law d (ν 0)) n
      = ∑ s ∈ Finset.range n, Parking.S (Parking.law d (ν 0)) s :=
    meanU_eq_sum_S (μ := LatticeProb.iidLaw d (ν 0)) hd (fun v => iidLaw_map_shiftConf' (ν 0) v)
      (integrable_eval_iid (d := d) (ν 0) hint0 0) n
  rw [hsumd, hsumc]
  have hterm : ∀ s ∈ Finset.range n, Parking.S (Parking.law d (ν 0)) s - K * δ
      ≤ Parking.S (Parking.law d (ν δ)) s := fun s _ => S_ge_of_nearFamily hd hfam' hδ s
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

end Parking
end

noncomputable section
namespace Parking
variable {d : ℕ}

/-- **The lower bound of `thm:near` from dimension four on** (`parking.tex:2896-2912`),
in the limit mean.  The critical law grows like `c log n`, the family at `δ` loses at
most `n K δ` of that growth, and the horizon `n = ⌈1/δ⌉` makes the loss bounded while
`log n ≥ log(e/δ) - 1`. -/
theorem exists_meanUlimit_log_lower (hd : 1 ≤ d) {δ₀ : ℝ} {ν : ℝ → Measure ℤ} {θ M K : ℝ}
    (hfam : NearFamily δ₀ ν θ M K) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ δ₁ ≤ δ₀ ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) δ₁,
      ENNReal.ofReal (c * Real.log (Real.exp 1 / δ))
        ≤ Parking.meanUlimit (Parking.law d (ν δ)) := by
  have hfam' : NearFamily δ₀ ν θ M K := hfam
  obtain ⟨hδ₀, hθ, hprob, hmean, hnc, hexp, hcouple⟩ := hfam
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) δ₀ := ⟨le_rfl, hδ₀.le⟩
  haveI hp0 := hprob 0 h0mem
  have hint0 : Integrable (fun k : ℤ => |(k : ℝ)|) (ν 0) :=
    integrable_abs_of_absMoment hθ (hexp 0 h0mem).1
  have hmean0 : ∫ k, (k : ℝ) ∂(ν 0) = 0 := by
    rw [hmean 0 h0mem]; ring
  obtain ⟨c₀, hc₀, hcd⟩ := Parking.Frozen.critical_density
  obtain ⟨-, C₀, hC₀, hlog⟩ := hcd d hd (ν 0) hp0 hnc hint0 hmean0
  -- the coupling constant is nonnegative
  have hK : 0 ≤ K := by
    obtain ⟨pri, hpri, hf, hs, hKd⟩ := hcouple δ₀ ⟨hδ₀, le_rfl⟩
    have hnn : (0 : ℝ) ≤ ∫ p, |((p.1 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ)| ∂pri :=
      integral_nonneg fun p => abs_nonneg _
    nlinarith
  set D : ℝ := c₀ + C₀ + K + K with hD
  have hD0 : 0 < D := by positivity
  set B : ℝ := 2 * D / c₀ with hB
  set δ₁ : ℝ := min (min δ₀ (1 / 2)) (Real.exp (1 - B)) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (lt_min hδ₀ (by norm_num)) (Real.exp_pos _)
  refine ⟨c₀ / 2, δ₁, by positivity, hδ₁0, le_trans (min_le_left _ _) (min_le_left _ _), ?_⟩
  intro δ hδ
  have hδ0 : 0 < δ := hδ.1
  have hδhalf : δ ≤ 1 / 2 := le_trans hδ.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδδ₀ : δ ≤ δ₀ := le_trans hδ.2 (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδexp : δ ≤ Real.exp (1 - B) := le_trans hδ.2 (min_le_right _ _)
  have hδ1 : δ ≤ 1 := by linarith
  -- the horizon
  set n : ℕ := Nat.ceil δ⁻¹ with hn
  have hinv2 : (2 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ0]
    linarith
  have hnge : δ⁻¹ ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  have hn2 : 2 ≤ n := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := le_trans hinv2 hnge
    exact_mod_cast h2
  have hnle : (n : ℝ) ≤ δ⁻¹ + 1 := by
    rw [hn]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
  have hlow := hlog n hn2
  have hcomp := meanU_ge_of_nearFamily hd hfam' ⟨hδ0, hδδ₀⟩ n
  have hLdef : Real.log (Real.exp 1 / δ) = 1 - Real.log δ := by
    rw [Real.log_div (Real.exp_ne_zero 1) (ne_of_gt hδ0), Real.log_exp]
  have hlogn : Real.log (Real.exp 1 / δ) - 1 ≤ Real.log n := by
    rw [hLdef]
    have h1 : Real.log δ⁻¹ ≤ Real.log n := Real.log_le_log (by positivity) hnge
    rw [Real.log_inv] at h1
    linarith
  have hLB : B ≤ Real.log (Real.exp 1 / δ) := by
    rw [hLdef]
    have h2 := Real.log_le_log hδ0 hδexp
    rw [Real.log_exp] at h2
    linarith
  have hloss : (n : ℝ) * (K * δ) ≤ K + K := by
    have h1 : (n : ℝ) * (K * δ) ≤ (δ⁻¹ + 1) * (K * δ) :=
      mul_le_mul_of_nonneg_right hnle (by positivity)
    have h2 : (δ⁻¹ + 1) * (K * δ) = K + K * δ := by
      field_simp
    have h3 : K * δ ≤ K := by nlinarith
    linarith
  have hDL : D ≤ c₀ / 2 * Real.log (Real.exp 1 / δ) := by
    rw [hB, div_le_iff₀ hc₀] at hLB
    linarith
  have hmain : c₀ / 2 * Real.log (Real.exp 1 / δ)
      ≤ Parking.meanU (Parking.law d (ν δ)) n := by
    have hstep : c₀ * (Real.log (Real.exp 1 / δ) - 1) ≤ c₀ * Real.log n :=
      mul_le_mul_of_nonneg_left hlogn hc₀.le
    have hDdef : D = c₀ + C₀ + K + K := hD
    nlinarith [hlow, hcomp, hloss, hstep, hDL]
  have hδmem : δ ∈ Set.Icc (0 : ℝ) δ₀ := ⟨hδ0.le, hδδ₀⟩
  haveI := hprob δ hδmem
  have hintd : Integrable (fun k : ℤ => |(k : ℝ)|) (ν δ) :=
    integrable_abs_of_absMoment hθ (hexp δ hδmem).1
  exact le_trans (ENNReal.ofReal_le_ofReal hmain)
    (ofReal_meanU_le_meanUlimit hd (ν δ) hintd n)

end Parking
end
