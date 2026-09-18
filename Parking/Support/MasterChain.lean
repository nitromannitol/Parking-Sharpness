/-
`thm:master` (`parking.tex:159-168`, proved at `parking.tex:1458-1464`) reduced
to `cor:critical`.

The upper bound IS the first display of `thm:upper`, which is SEALED.  The lower
bound is `cor:critical` in two pieces: past a threshold the logarithmic bound
dominates the constant it carries, and below the threshold the paper covers the
finitely many horizons by decreasing the constant, which it can do because
`E U_n(0) >= E U_1(0) = E eta(0)^+ > 0`.

The positive quantity is `S_0`, the mean number of particles started at the
origin and still active after no rounds at all, which is the mean positive part
of the configuration there; `lem:transport` makes it a lower bound on the mean
odometer at every horizon, and it is positive because a nonconstant mean-zero
law puts mass above the origin.

Below the threshold the argument needs no maximum over the finitely many
horizons: the logarithm is at most its value at the threshold, so one constant
covers them all.
-/
import Parking.Support.CriticalChain
import Parking.Frozen.Upper
import Parking.Support.CovParts

noncomputable section
open MeasureTheory Filter
namespace Parking
open LatticeProb
variable {d : ℕ}

/-! ### The survivor count at time zero -/

/-- Every particle started at a site is active after no rounds. -/
theorem survivorsFrom_zero (D : Driver d) (y : Site d) :
    LatticeProb.survivorsFrom D 0 y = (D.eta y).toNat := by
  unfold LatticeProb.survivorsFrom
  have hfil : (Finset.range (D.eta y).toNat).filter
      (fun i => (LatticeProb.state D 0).active (y, i)) = Finset.range (D.eta y).toNat := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    simp only [LatticeProb.state, LatticeProb.initial, Finset.mem_range] at hi ⊢
    simpa using hi
  rw [hfil, Finset.card_range]

/-- The marginal of the law of the data at one site is the one-site law. -/
theorem law_map_eval (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (z : Site d) :
    (law d ν).map (fun ω : Data d => ω.1 z) = ν := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  have h1 : (fun ω : Data d => ω.1 z) = (fun η : Site d → ℤ => η z) ∘ Prod.fst := rfl
  have h2 : (law d ν).map Prod.fst = LatticeProb.iidLaw d ν :=
    dataLaw_map_fst hd (LatticeProb.iidLaw d ν)
  rw [h1, ← Measure.map_map (measurable_pi_apply z) measurable_fst, h2]
  exact Measure.infinitePi_map_eval _ z

/-- `S_0` is the mean positive part of the configuration at the origin. -/
theorem S_zero_eq (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    S (law d ν) 0 = ∫ k, ((k.toNat : ℕ) : ℝ) ∂ν := by
  have hpt : ∀ ω : Data d,
      ((LatticeProb.survivorsFrom (toDriver ω) 0 0 : ℕ) : ℝ) = (((ω.1 0).toNat : ℕ) : ℝ) := by
    intro ω; rw [survivorsFrom_zero]; rfl
  show ∫ ω, ((LatticeProb.survivorsFrom (toDriver ω) 0 0 : ℕ) : ℝ) ∂(law d ν) = _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hm : Measurable (fun ω : Data d => ω.1 (0 : Site d)) :=
    (measurable_pi_apply (0 : Site d)).comp measurable_fst
  conv_rhs => rw [← law_map_eval hd ν (0 : Site d)]
  rw [integral_map hm.aemeasurable
    ((measurable_int_fun (fun k : ℤ => ((k.toNat : ℕ) : ℝ))).aestronglyMeasurable)]

/-- A nonconstant law of mean zero has a positive mean positive part. -/
theorem integral_toNat_pos (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnc : ∀ k : ℤ, ν {k} ≠ 1) (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν)
    (hmean : ∫ k, (k : ℝ) ∂ν = 0) :
    0 < ∫ k, ((k.toNat : ℕ) : ℝ) ∂ν := by
  have hnn : ∀ k : ℤ, (0 : ℝ) ≤ ((k.toNat : ℕ) : ℝ) := fun k => Nat.cast_nonneg _
  have hle : ∀ k : ℤ, ((k.toNat : ℕ) : ℝ) ≤ |(k : ℝ)| := by
    intro k
    rcases le_or_gt k 0 with hk | hk
    · rw [Int.toNat_of_nonpos hk]; simp
    · have h1 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk.le
      have h2 : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast congrArg (fun m : ℤ => (m : ℝ)) h1
      rw [h2, abs_of_pos (by exact_mod_cast hk)]
  have hI : Integrable (fun k : ℤ => ((k.toNat : ℕ) : ℝ)) ν := by
    refine Integrable.mono' hint (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn k)]
    exact hle k
  rcases (integral_nonneg (fun k => hnn k) : (0:ℝ) ≤ ∫ k, ((k.toNat : ℕ) : ℝ) ∂ν).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hae : (fun k : ℤ => ((k.toNat : ℕ) : ℝ)) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun k => hnn k) hI).mp h.symm
    -- the coordinate is nonpositive almost surely
    have hnegint : Integrable (fun k : ℤ => -(k : ℝ)) ν := by
      refine Integrable.mono' hint (measurable_int_fun _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun k => ?_)
      rw [Real.norm_eq_abs, abs_neg]
    have hnonneg : ∀ᵐ (k : ℤ) ∂ν, 0 ≤ -(k : ℝ) := by
      filter_upwards [hae] with k hk
      have : ((k.toNat : ℕ) : ℝ) = 0 := hk
      have hk0 : k.toNat = 0 := by exact_mod_cast this
      have : k ≤ 0 := Int.toNat_eq_zero.mp hk0
      have : (k : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
    have hintneg : ∫ k, -(k : ℝ) ∂ν = 0 := by rw [integral_neg, hmean, neg_zero]
    have hzero : (fun k : ℤ => -(k : ℝ)) =ᵐ[ν] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hnegint).mp hintneg
    have hall : ∀ᵐ k ∂ν, k = 0 := by
      filter_upwards [hzero] with k hk
      have : -(k : ℝ) = 0 := hk
      have : (k : ℝ) = 0 := by linarith
      exact_mod_cast this
    have hcompl : ν {k : ℤ | k ≠ 0} = 0 := by
      have : {k : ℤ | ¬ (k = 0)} = {k : ℤ | k ≠ 0} := rfl
      rw [← this]
      exact ae_iff.mp hall
    have hsingle : ν {(0 : ℤ)} = 1 := by
      have huniv : ν Set.univ = 1 := measure_univ
      have hsplit : (Set.univ : Set ℤ) = {(0 : ℤ)} ∪ {k : ℤ | k ≠ 0} := by
        ext k; by_cases hk : k = 0 <;> simp [hk]
      have hle2 : ν Set.univ ≤ ν {(0 : ℤ)} + ν {k : ℤ | k ≠ 0} := by
        rw [hsplit]; exact measure_union_le _ _
      rw [huniv, hcompl, add_zero] at hle2
      exact le_antisymm (by simpa using prob_le_one) hle2
    exact hnc 0 hsingle

/-- `S_0 ≤ E U_n(0)` for every positive horizon. -/
theorem S_zero_le_meanU (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) (n : ℕ) (hn : 1 ≤ n) :
    S (law d ν) 0 ≤ meanU (law d ν) n := by
  have hexpn := (Parking.Frozen.transport d hd ν ‹IsProbabilityMeasure ν› hint).2.1
  rw [hexpn n]
  exact Finset.single_le_sum (f := fun s => S (law d ν) s)
    (fun s _ => S_nonneg _ s) (Finset.mem_range.mpr hn)

/-! ### `thm:master` from `cor:critical` -/

/-- **`thm:master` reduced to `cor:critical`.**  Applying this to
`Parking.Frozen.cor_critical` proves `Parking.Frozen.master`. -/
theorem master_of_cor_critical
    (hcc : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (ν : Measure ℤ), IsProbabilityMeasure ν →
      (∀ k : ℤ, ν {k} ≠ 1) → Integrable (fun k : ℤ => |(k : ℝ)|) ν →
      ∫ k, (k : ℝ) ∂ν = 0 →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
        max (Parking.meanu (Parking.law d ν) n) (c * Real.log n - C)
          ≤ Parking.meanU (Parking.law d ν) n)
    (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hprob : IsProbabilityMeasure ν)
    (hnonconst : ∀ k : ℤ, ν {k} ≠ 1) (hmean : ∫ k, (k : ℝ) ∂ν = 0)
    (θ : ℝ) (hθ : 0 < θ) (hexp : Integrable (fun k : ℤ => Real.exp (θ * |(k : ℝ)|)) ν) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c * (Parking.meanu (Parking.law d ν) n + Real.log n) ≤ Parking.meanU (Parking.law d ν) n ∧
        Parking.meanU (Parking.law d ν) n
          ≤ C * (Parking.meanu (Parking.law d ν) n + Real.log n) := by
  haveI := hprob
  -- the exponential moment gives a first moment
  have hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν := by
    obtain ⟨K, hK, hbound⟩ := rpow_le_const_mul_exp (r := (1 : ℝ)) (by norm_num) hθ
    refine Integrable.mono' (hexp.const_mul K) (measurable_int_fun _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => ?_)
    have h0 : (0 : ℝ) ≤ |((k : ℤ) : ℝ)| := abs_nonneg _
    have hb := hbound _ h0
    rw [Real.rpow_one] at hb
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hb
  have hν : CriticalLaw ν := ⟨hprob, hnonconst, hmean, ⟨θ, hθ, hexp⟩⟩
  obtain ⟨Cu, hCu, hupper, -⟩ :=
    Parking.Frozen.upper hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
  obtain ⟨c₀, hc₀, hall⟩ := hcc
  obtain ⟨C₀, hC₀, hmax⟩ := hall d hd ν hprob hnonconst hint hmean
  set m : ℝ := S (law d ν) 0 with hm
  have hmpos : 0 < m := by
    rw [hm, S_zero_eq hd ν]
    exact integral_toNat_pos ν hnonconst hint hmean
  set L : ℝ := max (2 * C₀ / c₀) 1 with hL
  have hL1 : (1 : ℝ) ≤ L := le_max_right _ _
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  set c : ℝ := min (min (1 / 2) (c₀ / 4)) (m / (2 * L)) with hc
  have hcle1 : c ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcle2 : c ≤ c₀ / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcle3 : c ≤ m / (2 * L) := min_le_right _ _
  have hcpos : 0 < c := by
    refine lt_min (lt_min (by norm_num) (by linarith)) ?_
    have : (0 : ℝ) < 2 * L := by linarith
    exact div_pos hmpos this
  refine ⟨c, max Cu c, hcpos, le_max_right _ _, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  have hmeanu0 : (0 : ℝ) ≤ meanu (law d ν) n :=
    integral_nonneg fun ω => uOf_nonneg ω n 0
  have hAQ : meanu (law d ν) n ≤ meanU (law d ν) n :=
    le_trans (le_max_left _ _) (hmax n hn)
  have hLQ : c₀ * Real.log n - C₀ ≤ meanU (law d ν) n :=
    le_trans (le_max_right _ _) (hmax n hn)
  have hmQ : m ≤ meanU (law d ν) n := S_zero_le_meanU hd ν hint n (by omega)
  refine ⟨?_, ?_⟩
  · rcases le_or_gt L (Real.log n) with hcase | hcase
    · -- past the threshold the logarithmic bound dominates its constant
      have hthr : 2 * C₀ / c₀ ≤ Real.log n := le_trans (le_max_left _ _) hcase
      have hC0 : C₀ ≤ c₀ / 2 * Real.log n := by
        rw [div_le_iff₀ hc₀] at hthr
        linarith
      nlinarith [hAQ, hLQ, hmeanu0, hlogn, hcle1, hcle2, hc₀]
    · -- below the threshold the mean survivor count at time zero covers the horizon
      have hcl : c * Real.log n ≤ m / 2 := by
        have h1 : c * Real.log n ≤ c * L := by nlinarith [hcpos, hcase.le]
        have h2 : c * L ≤ m / 2 := by
          have h2L : (0 : ℝ) < 2 * L := by linarith
          rw [le_div_iff₀ h2L] at hcle3
          linarith
        linarith
      nlinarith [hAQ, hmQ, hmeanu0, hcle1, hcpos]
  · have hup := (hupper n hn).2
    have hsum : (0 : ℝ) ≤ meanu (law d ν) n + Real.log n := by linarith
    have hC : Cu ≤ max Cu c := le_max_left _ _
    nlinarith [hup, hsum, hC]

end Parking
end
