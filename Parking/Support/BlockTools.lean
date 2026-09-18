/-
The analytic tools of Step 2 of `lem:mean-horizon` (`parking.tex:2802-2826`).

Step 2 turns the block decomposition of `Parking/Support/BlockStop.lean` into a
number.  Four elementary facts do it.

* The odometer commutes with translation (`u_shift`), which is how "the walk is
  independent of `ξ_δ`, so stationarity gives …" is read here: the moment of
  `u_{ℓ}(X_{s};ξ_δ)` does not depend on where the walk stands.
* Hölder's inequality with the exponents `5/4` and `5` splits
  `E[1_{σ>s} u_ℓ(X_s)]` into `P(σ>s)^{4/5}` and the fifth moment norm
  (`integral_ite_le_holder`).
* Markov's inequality bounds `P(σ>s)` by `E σ / s` (`measureReal_gt_le_div`).
* The scale `φ_d` does not see a shift of its argument by two
  (`phi_add_two_le`), which is what turns `φ_d(N)` with `N = 1 ∨ ⌈M⌉` back into
  `φ_d(M)`.
-/
import Parking.Support.BlockStop
import Parking.Support.UpperStep
import Parking.Support.PhiSum

noncomputable section

namespace Parking

open MeasureTheory LatticeProb

variable {d : ℕ}

theorem u_shift (_hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (y x : Site d) :
    u (fun z => η (z + y)) n x = u η n (x + y) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      show max 0 (η (x + y) + walkOp (u (fun z => η (z + y)) n) x)
        = max 0 (η (x + y) + walkOp (u η n) (x + y))
      congr 2
      show (∑ i : Fin d, (u (fun z => η (z + y)) n (x + unit i)
            + u (fun z => η (z + y)) n (x - unit i))) / (2 * (d : ℝ))
        = (∑ i : Fin d, (u η n (x + y + unit i) + u η n (x + y - unit i))) / (2 * (d : ℝ))
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (x + unit i), ih (x - unit i)]
      congr 2 <;> abel

theorem phi_add_two_le (d : ℕ) {M : ℝ} (hM : 0 ≤ M) : phi d (M + 2) ≤ 3 * phi d M := by
  simp only [phi]
  split_ifs with h
  · have hd3 : (d:ℝ) ≤ 3 := by exact_mod_cast h
    have he0 : (0:ℝ) ≤ (4 - (d:ℝ))/4 := by linarith
    have he1 : (4 - (d:ℝ))/4 ≤ 1 := by
      have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
      linarith
    have hbase : M + 2 + 1 ≤ 3 * (M + 1) := by linarith
    have h1 : (M + 2 + 1) ^ ((4 - (d:ℝ))/4) ≤ (3 * (M + 1)) ^ ((4 - (d:ℝ))/4) :=
      Real.rpow_le_rpow (by linarith) hbase he0
    have h2 : (3 * (M + 1)) ^ ((4 - (d:ℝ))/4)
        = (3:ℝ) ^ ((4 - (d:ℝ))/4) * (M + 1) ^ ((4 - (d:ℝ))/4) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h3 : (3:ℝ) ^ ((4 - (d:ℝ))/4) ≤ (3:ℝ) ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
    rw [Real.rpow_one] at h3
    have h4 : (0:ℝ) ≤ (M + 1) ^ ((4 - (d:ℝ))/4) := Real.rpow_nonneg (by linarith) _
    nlinarith [h1, h2, h3, h4]
  · have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hb : Real.log (M + 2 + 2) ≤ Real.log (2 * (M + 2)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at hb
    have hc : Real.log 2 ≤ Real.log (M + 2) := Real.log_le_log (by norm_num) (by linarith)
    linarith

/-! ### Hölder and Markov -/

/-- **Hölder's inequality with exponents `5/4` and `5`**, in the form Step 2 uses it:
the reward collected on an event is at most the chance of the event to the power `1 - 1/5`
times the fifth moment norm. -/
theorem integral_ite_le_holder {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {A : Set Ω} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    {f : Ω → ℝ}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfm : AEStronglyMeasurable f μ)
    (hf : Integrable (fun ω => |f ω| ^ (5:ℝ)) μ) :
    ∫ ω, (if ω ∈ A then f ω else 0) ∂μ
      ≤ (μ.real A) ^ ((4:ℝ)/5) * (∫ ω, |f ω| ^ (5:ℝ) ∂μ) ^ ((1:ℝ)/5) := by
  classical
  set g : Ω → ℝ := Set.indicator A (fun _ => (1:ℝ)) with hg
  have hconj : Real.HolderConjugate (5/4) 5 := by constructor <;> norm_num
  have hg0 : 0 ≤ᵐ[μ] g := Filter.Eventually.of_forall fun ω => by
    rw [hg]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hf0' : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall hf0
  have hgmem : MemLp g (ENNReal.ofReal (5/4)) μ :=
    MemLp.indicator hA (memLp_const (1:ℝ))
  have hfmem : MemLp f (ENNReal.ofReal 5) μ :=
    ⟨hfm, lt_top_iff_ne_top.mpr (eLpNorm_ne_top μ (by norm_num) f hf)⟩
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg hconj hg0 hf0' hgmem hfmem
  have hpt : ∀ ω : Ω, g ω * f ω = if ω ∈ A then f ω else 0 := by
    intro ω
    rw [hg]
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, if_pos h, one_mul]
    · rw [Set.indicator_of_notMem h, if_neg h, zero_mul]
  have hgpow : ∀ ω : Ω, g ω ^ (5/4 : ℝ) = Set.indicator A (1 : Ω → ℝ) ω := by
    intro ω
    rw [hg]
    by_cases h : ω ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Real.one_rpow]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        Real.zero_rpow (by norm_num)]
  have hfpow : ∀ ω : Ω, f ω ^ (5:ℝ) = |f ω| ^ (5:ℝ) := by
    intro ω; rw [abs_of_nonneg (hf0 ω)]
  simp only [hpt, hgpow, hfpow] at hmain
  rw [integral_indicator_one hA] at hmain
  refine hmain.trans (le_of_eq ?_)
  congr 2
  norm_num

/-- **Markov's inequality** for the stopping time: the chance that it passes `s` is at
most its mean over `s`. -/
theorem measureReal_gt_le_div {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω) (hf : Integrable f μ)
    {s : ℝ} (hs : 0 < s) :
    μ.real {ω | s < f ω} ≤ (∫ ω, f ω ∂μ) / s := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hf s
  have hsub : {ω | s < f ω} ⊆ {ω | s ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact le_of_lt hω
  have hmono : μ.real {ω | s < f ω} ≤ μ.real {ω | s ≤ f ω} := by
    refine measureReal_mono hsub ?_
    exact measure_ne_top μ _
  rw [le_div_iff₀ hs, mul_comm]
  nlinarith [h, hmono, measureReal_nonneg (μ := μ) (s := {ω | s < f ω})]

end Parking

end
