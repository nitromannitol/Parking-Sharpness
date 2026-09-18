/-
The proof of `prop:w-moment`.

The two displays are assembled here from the four pieces the paper's proof
names: the martingale of `lem:w-martingale` with the increment bound
`eq:increment`, the martingale moment inequality applied to the first `k`
increments and passed to the limit by Fatou's lemma, the convexity that turns
the lattice sum of the quadratic variation into the moment at the origin, and
Jensen's inequality for the walk average.
-/
import Parking.Support.WStarMoment
import Parking.Support.GreenIncrement
import Parking.Frozen.WMartingale
import Parking.Frozen.GammaSum
import Parking.External.Bernstein

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset

variable {d : ℕ}

/-! ### A term of a bounded family is below its supremum over an initial segment -/

theorem le_iSup_Iic {n : ℕ} {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hbd : ∀ m ≤ n, f m ≤ B)
    {m : ℕ} (hm : m ≤ n) : f m ≤ ⨆ k ∈ Set.Iic n, f k := by
  have hbdd : BddAbove (Set.range fun k : ℕ => ⨆ _ : k ∈ Set.Iic n, f k) :=
    ⟨B, by rintro x ⟨k, rfl⟩; exact iSup_mem_le hB hbd k⟩
  calc f m = ⨆ _ : m ∈ Set.Iic n, f m :=
        (ciSup_pos (f := fun _ : m ∈ Set.Iic n => f m) (Set.mem_Iic.mpr hm)).symm
    _ ≤ _ := le_ciSup hbdd m

/-! ### The moments of the error are bounded over an initial segment -/

theorem exists_wErr_moment_bound (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ m ≤ n,
      (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r) ≤ B := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set A : ℝ := wCoef d n ^ r * ∫ ω, confBox ω 0 (2 * n) ^ r ∂(law d ν) with hA
  have hAint : Integrable (fun ω : Data d => confBox ω 0 (2 * n) ^ r) (law d ν) :=
    integrable_confBox_rpow hd ν hθ hexp hr 0 (2 * n)
  have hA0 : 0 ≤ A := by
    refine mul_nonneg (Real.rpow_nonneg (wCoef_nonneg d n) r) ?_
    exact integral_nonneg fun ω => Real.rpow_nonneg (confBox_nonneg ω 0 (2 * n)) r
  refine ⟨A ^ (1 / r), Real.rpow_nonneg hA0 _, fun m hm => ?_⟩
  refine Real.rpow_le_rpow
    (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r) ?_ (by positivity)
  have hptw : ∀ ω : Data d,
      |wErr ω m 0| ^ r ≤ wCoef d n ^ r * confBox ω 0 (2 * n) ^ r := by
    intro ω
    rw [← Real.mul_rpow (wCoef_nonneg d n) (confBox_nonneg ω 0 (2 * n))]
    refine Real.rpow_le_rpow (abs_nonneg _) ?_ (le_trans zero_le_one hr)
    refine le_trans (abs_wErr_le hd ω m 0) ?_
    refine mul_le_mul (wCoef_mono d hm) (confBox_mono ω 0 (by omega))
      (confBox_nonneg _ _ _) (wCoef_nonneg d n)
  calc ∫ ω, |wErr ω m 0| ^ r ∂(law d ν)
      ≤ ∫ ω, wCoef d n ^ r * confBox ω 0 (2 * n) ^ r ∂(law d ν) :=
        integral_mono (integrable_abs_wErr_rpow hd ν hθ hexp hr m 0) (hAint.const_mul _) hptw
    _ = A := by rw [hA, integral_const_mul]

/-! ### The second display of `prop:w-moment` -/

theorem wStar_moment_bound (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) :
    (∫ ω, wStar ω n 0 ^ r ∂(law d ν)) ^ (1 / r)
      ≤ ((n : ℝ) + 1) ^ (1 / r) * ⨆ m ∈ Set.Iic n,
          (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  set M : ℕ → ℝ := fun m => ∫ ω, |wErr ω m 0| ^ r ∂(law d ν) with hM
  have hMnn : ∀ m, 0 ≤ M m := fun m =>
    integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
  obtain ⟨B, hB0, hB⟩ := exists_wErr_moment_bound hd ν hθ hexp hr n
  set S : ℝ := ⨆ m ∈ Set.Iic n, M m ^ (1 / r) with hS
  have hS0 : 0 ≤ S := iSup_Iic_nonneg hB0 hB
  have hMS : ∀ m ≤ n, M m ≤ S ^ r := by
    intro m hm
    have h1 : M m ^ (1 / r) ≤ S := le_iSup_Iic hB0 hB hm
    have h2 : (M m ^ (1 / r)) ^ r ≤ S ^ r :=
      Real.rpow_le_rpow (Real.rpow_nonneg (hMnn m) _) h1 (le_of_lt hr0)
    rwa [← Real.rpow_mul (hMnn m), one_div, inv_mul_cancel₀ (ne_of_gt hr0),
      Real.rpow_one] at h2
  have hint : Integrable (fun ω : Data d =>
      ∑ j ∈ Finset.range (n + 1), wWalkMoment (d := d) r (n - j) j ω) (law d ν) :=
    integrable_finsetSum _ fun j _ => integrable_wWalkMoment hd ν hθ hexp hr (n - j) j
  have hle : ∫ ω, wStar ω n 0 ^ r ∂(law d ν) ≤ ((n : ℝ) + 1) * S ^ r := by
    calc ∫ ω, wStar ω n 0 ^ r ∂(law d ν)
        ≤ ∫ ω, (∑ j ∈ Finset.range (n + 1), wWalkMoment (d := d) r (n - j) j ω)
            ∂(law d ν) :=
          integral_mono (integrable_wStar_rpow hd ν hθ hexp hr n 0) hint
            fun ω => wStar_rpow_le_sum hd ν hr n ω
      _ = ∑ j ∈ Finset.range (n + 1),
            ∫ ω, wWalkMoment (d := d) r (n - j) j ω ∂(law d ν) :=
          integral_finsetSum _ fun j _ => integrable_wWalkMoment hd ν hθ hexp hr (n - j) j
      _ = ∑ j ∈ Finset.range (n + 1), M (n - j) :=
          Finset.sum_congr rfl fun j _ => integral_wWalkMoment hd ν hθ hexp hr (n - j) j
      _ ≤ ∑ _j ∈ Finset.range (n + 1), S ^ r :=
          Finset.sum_le_sum fun j _ => hMS (n - j) (Nat.sub_le n j)
      _ = ((n : ℝ) + 1) * S ^ r := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have h2 : (∫ ω, wStar ω n 0 ^ r ∂(law d ν)) ^ (1 / r)
      ≤ (((n : ℝ) + 1) * S ^ r) ^ (1 / r) :=
    Real.rpow_le_rpow
      (integral_nonneg fun ω => Real.rpow_nonneg (wStar_nonneg ω n 0) r) hle (by positivity)
  rwa [Real.mul_rpow (by positivity) (Real.rpow_nonneg hS0 r), ← Real.rpow_mul hS0,
    mul_one_div, div_self (ne_of_gt hr0), Real.rpow_one] at h2


/-! ### The weights of the quadratic variation -/

/-- `sup_{j ≤ n} Γ_j(y)`, the weight of the site `y` in the paper's bound on the
predictable quadratic variation. -/
def gammaSup (d n : ℕ) (y : Site d) : ℝ := ⨆ j ∈ Set.Iic n, gamma d j y

theorem gammaSup_nonneg (hd : 1 ≤ d) (n : ℕ) (y : Site d) : 0 ≤ gammaSup d n y :=
  iSup_gamma_Iic_nonneg hd n y

theorem gamma_le_gammaSup (hd : 1 ≤ d) {n m : ℕ} (hm : m ≤ n) (y : Site d) :
    gamma d m y ≤ gammaSup d n y :=
  le_iSup_gamma_Iic hd (Set.mem_Iic.mpr hm) y

theorem gammaSup_mono (hd : 1 ≤ d) {m n : ℕ} (h : m ≤ n) (y : Site d) :
    gammaSup d m y ≤ gammaSup d n y :=
  iSup_Iic_le (gammaSup_nonneg hd n y) fun _j hj => gamma_le_gammaSup hd (le_trans hj h) y

/-- The total weight over the box of radius `n`. -/
def gammaTot (d n : ℕ) : ℝ := ∑ y ∈ boxFinset (0 : Site d) n, gammaSup d n y

theorem gammaTot_nonneg (hd : 1 ≤ d) (n : ℕ) : 0 ≤ gammaTot d n :=
  Finset.sum_nonneg fun y _ => gammaSup_nonneg hd n y

/-! ### The quadratic variation against the odometer over a box -/

/-- The paper's `∑_y (sup_{j ≤ n} Γ_j(y)) U_n(y)`, over the box outside which
every `Γ_j` with `j ≤ n` vanishes. -/
def qvBound (d n : ℕ) (ω : Data d) : ℝ :=
  ∑ y ∈ boxFinset (0 : Site d) n, gammaSup d n y * ((U ω n y : ℕ) : ℝ)

theorem qvBound_nonneg (hd : 1 ≤ d) (n : ℕ) (ω : Data d) : 0 ≤ qvBound d n ω :=
  Finset.sum_nonneg fun y _ => mul_nonneg (gammaSup_nonneg hd n y) (Nat.cast_nonneg _)

theorem qv_le_qvBound (hd : 1 ≤ d) {m n : ℕ} (hmn : m ≤ n) (ω : Data d) :
    ∑ s ∈ Finset.Icc 1 (m - 1), ∑' y : Site d,
        ((A ω (s - 1) y : ℕ) : ℝ) * gamma d (m - s) y
      ≤ qvBound d n ω := by
  classical
  have hfin : ∀ s : ℕ, (∑' y : Site d, ((A ω (s - 1) y : ℕ) : ℝ) * gamma d (m - s) y)
      = ∑ y ∈ boxFinset (0 : Site d) n, ((A ω (s - 1) y : ℕ) : ℝ) * gamma d (m - s) y := by
    intro s
    refine tsum_eq_sum fun y hy => ?_
    rw [gamma_eq_zero_of_notMem_box
      (fun hc => hy (boxFinset_mono (le_trans (Nat.sub_le m s) hmn) hc)), mul_zero]
  rw [Finset.sum_congr rfl (fun s _ => hfin s), Finset.sum_comm]
  refine Finset.sum_le_sum fun y _ => ?_
  refine le_trans (qv_le_pointwise hd m ω y) ?_
  refine mul_le_mul (gammaSup_mono hd hmn y) ?_ (Nat.cast_nonneg _) (gammaSup_nonneg hd n y)
  exact Nat.cast_le.mpr (LatticeProb.particleOdometer_mono (toDriver ω) y hmn)

/-! ### The moment of the bound -/

theorem integral_U_rpow_shift (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {r : ℝ} (hr : 1 ≤ r) (n : ℕ) (y : Site d) :
    ∫ ω, ((U ω n y : ℕ) : ℝ) ^ r ∂(law d ν)
      = ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν) := by
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => ν))
  have hti : TranslationInvariant (LatticeProb.iidLaw d ν) := fun w =>
    iidLaw_map_shiftConf' ν w
  have hlaw : law d ν = dataLaw d (LatticeProb.iidLaw d ν) := rfl
  have hAE : AEStronglyMeasurable (fun ω : Data d => ((U ω n y : ℕ) : ℝ) ^ r)
      (dataLaw d (LatticeProb.iidLaw d ν)) := by
    rw [← hlaw]
    exact (integrable_U_rpow hd ν hθ hexp hr n y).aestronglyMeasurable
  have h := integral_comp_shiftData (μ := LatticeProb.iidLaw d ν) hd hti (-y) hAE
  rw [← hlaw] at h
  have hpt : ∀ ω : Data d, ((U (shiftData (-y) ω) n y : ℕ) : ℝ) ^ r
      = ((U ω n 0 : ℕ) : ℝ) ^ r := by
    intro ω
    rw [U_shiftData, add_neg_cancel]
  simp only [hpt] at h
  exact h.symm

theorem integral_qvBound_rpow_le (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    ∫ ω, qvBound d n ω ^ p ∂(law d ν)
      ≤ gammaTot d n ^ p * ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ p ∂(law d ν) := by
  classical
  set T : ℝ := gammaTot d n with hT
  have hT0 : 0 ≤ T := gammaTot_nonneg hd n
  set Mu : ℝ := ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ p ∂(law d ν) with hMu
  have hMu0 : 0 ≤ Mu := integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) p
  have hdiv : ∑ y ∈ boxFinset (0 : Site d) n, gammaSup d n y / T ≤ 1 := by
    rcases eq_or_lt_of_le hT0 with hTz | hTpos
    · have : ∀ y ∈ boxFinset (0 : Site d) n, gammaSup d n y / T = 0 := by
        intro y _
        rw [← hTz, div_zero]
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_zero]
      norm_num
    · have hTeq : ∑ y ∈ boxFinset (0 : Site d) n, gammaSup d n y = T := rfl
      rw [← Finset.sum_div, hTeq, div_self (ne_of_gt hTpos)]
  have hptw : ∀ ω : Data d, qvBound d n ω ^ p
      ≤ T ^ p * ∑ y ∈ boxFinset (0 : Site d) n,
          (gammaSup d n y / T) * ((U ω n y : ℕ) : ℝ) ^ p := by
    intro ω
    exact rpow_weighted_sum_le _ _ _ (fun y _ => gammaSup_nonneg hd n y)
      (fun y _ => Nat.cast_nonneg _) hp
  have hdomint : Integrable (fun ω : Data d => T ^ p * ∑ y ∈ boxFinset (0 : Site d) n,
      (gammaSup d n y / T) * ((U ω n y : ℕ) : ℝ) ^ p) (law d ν) :=
    (integrable_finsetSum _ fun y _ =>
      (integrable_U_rpow hd ν hθ hexp hp n y).const_mul _).const_mul _
  have hmono : ∫ ω, qvBound d n ω ^ p ∂(law d ν)
      ≤ ∫ ω, (T ^ p * ∑ y ∈ boxFinset (0 : Site d) n,
          (gammaSup d n y / T) * ((U ω n y : ℕ) : ℝ) ^ p) ∂(law d ν) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (qvBound_nonneg hd n ω) p)
      hdomint (Filter.Eventually.of_forall hptw)
  refine le_trans hmono ?_
  rw [integral_const_mul, integral_finsetSum _ fun y _ =>
    (integrable_U_rpow hd ν hθ hexp hp n y).const_mul _]
  have hterm : ∀ y ∈ boxFinset (0 : Site d) n,
      ∫ ω, (gammaSup d n y / T) * ((U ω n y : ℕ) : ℝ) ^ p ∂(law d ν)
        = (gammaSup d n y / T) * Mu := by
    intro y _
    rw [integral_const_mul, integral_U_rpow_shift hd ν hθ hexp hp n y]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hT0 p)
  calc (∑ y ∈ boxFinset (0 : Site d) n, gammaSup d n y / T) * Mu ≤ 1 * Mu :=
        mul_le_mul_of_nonneg_right hdiv hMu0
    _ = Mu := one_mul Mu

/-! ### The error vanishes at the first two horizons -/

theorem wErr_eq_zero_of_lt_two (ω : Data d) {m : ℕ} (hm : m < 2) (x : Site d) :
    wErr ω m x = 0 := by
  interval_cases m
  · rfl
  · have hU : ∀ y : Site d, U ω 0 y = 0 := by
      intro y; rw [U_eq_sum_A]; simp
    have hexp : wErr ω 1 x
        = walkOp (wErr ω 0) x +
          ∑ y ∈ nbrFinset x,
            ((arrivals ω.2.1 y x (U ω 0 y) : ℝ) - (U ω 0 y : ℝ) / (2 * (d : ℝ))) := rfl
    rw [hexp]
    have hwalk : walkOp (wErr ω 0) x = 0 := by
      have h0 : wErr ω (0 : ℕ) = fun _ : Site d => (0 : ℝ) := rfl
      rw [walkOp, nbrSum, h0]
      simp
    have hsum : ∑ y ∈ nbrFinset x,
        ((arrivals ω.2.1 y x (U ω 0 y) : ℝ) - (U ω 0 y : ℝ) / (2 * (d : ℝ))) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hU y]
      simp [arrivals]
    rw [hwalk, hsum, add_zero]

/-! ### Reindexing a sum over an interval -/

theorem sum_Icc_shift (g : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, g (i - 1) = ∑ j ∈ Finset.range k, g j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, Nat.add_sub_cancel]


/-! ### Auxiliary facts for the first display -/

theorem kappa_nonneg (d n : ℕ) : 0 ≤ kappa d n := by
  rw [kappa]
  split_ifs with h1 h2
  · positivity
  · refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · norm_num

theorem gammaTot_le (hd : 1 ≤ d) {Cg : ℝ}
    (hg : ∀ n : ℕ, 1 ≤ n →
      Summable (fun y : Site d => ⨆ m ∈ Set.Iic n, gamma d m y) ∧
        ∑' y : Site d, (⨆ m ∈ Set.Iic n, gamma d m y) ≤ Cg * kappa d n)
    {n : ℕ} (hn : 1 ≤ n) : gammaTot d n ≤ Cg * kappa d n := by
  obtain ⟨hsum, hle⟩ := hg n hn
  refine le_trans ?_ hle
  exact hsum.sum_le_tsum (boxFinset (0 : Site d) n) (fun y _ => gammaSup_nonneg hd n y)

theorem measurable_qvBound (n : ℕ) : Measurable fun ω : Data d => qvBound d n ω :=
  Finset.measurable_sum _ fun y _ =>
    ((measurable_from_countable' fun k : ℕ => (k : ℝ)).comp (measurable_U n y)).const_mul _

theorem integrable_qvBound_rpow (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν)
    {p : ℝ} (hp : 1 ≤ p) (n : ℕ) :
    Integrable (fun ω : Data d => qvBound d n ω ^ p) (law d ν) := by
  classical
  have hdom : Integrable (fun ω : Data d =>
      gammaTot d n ^ p * ∑ y ∈ boxFinset (0 : Site d) n,
        (gammaSup d n y / gammaTot d n) * ((U ω n y : ℕ) : ℝ) ^ p) (law d ν) :=
    (integrable_finsetSum _ fun y _ =>
      (integrable_U_rpow hd ν hθ hexp hp n y).const_mul _).const_mul _
  refine Integrable.mono' hdom
    (((measurable_rpow_const (le_trans zero_le_one hp)).comp
      (measurable_qvBound n)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (qvBound_nonneg hd n ω) p)]
  exact rpow_weighted_sum_le _ _ _ (fun y _ => gammaSup_nonneg hd n y)
    (fun y _ => Nat.cast_nonneg _) hp

/-! ### The first display of `prop:w-moment` -/

/-- **The constant of the first display of `prop:w-moment` does not depend on the law.**
It is built from the constant of `ext-bernstein`, the sum of `lem:gamma-sum` and the
increment bound of `lem:w-martingale`, all three of them functions of the dimension
alone, so one constant serves a whole family of laws at once. -/
theorem exists_wErr_moment_const_uniform (hd : 1 ≤ d)
    (hBern : Parking.External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : Measure ℤ, IsProbabilityMeasure ν → ∀ θ : ℝ, 0 < θ →
      Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν →
      ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (⨆ m ∈ Set.Iic n, (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * kappa d n *
            (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)) + r) := by
  classical
  obtain ⟨CB, hCB, hBern'⟩ := hBern
  obtain ⟨Cg, hCg, hgsum⟩ := Parking.Frozen.gamma_sum d hd
    (fun h2 => Parking.External.greenGradient d h2)
  obtain ⟨K, hK, hKle⟩ := exists_greenIncrement_le d hd
  have hCpos : (0 : ℝ) < CB * (Real.sqrt Cg + K + 1) :=
    mul_pos hCB (by nlinarith [Real.sqrt_nonneg Cg])
  refine ⟨CB * (Real.sqrt Cg + K + 1), hCpos, ?_⟩
  intro ν hprobν θ hθ hexp n hn r hr2
  haveI := hprobν
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hp1 : (1 : ℝ) ≤ r / 2 := by linarith
  haveI hinst : ∀ q : Site d × ℕ, IsProbabilityMeasure (instructionLaw (d := d) q.1) :=
    fun q => instructionLaw_isProbability hd q.1
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  set E : ℝ := ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν) with hEdef
  have hE0 : 0 ≤ E :=
    integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) r
  set D : ℝ := E ^ (1 / r) with hDdef
  have hD0 : 0 ≤ D := Real.rpow_nonneg hE0 _
  set X : ℝ := Real.sqrt (r * kappa d n * D) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  set RHS : ℝ := CB * (Real.sqrt Cg + K + 1) * (X + r) with hRHSdef
  have hRHS0 : 0 ≤ RHS := by
    rw [hRHSdef]
    have : (0 : ℝ) ≤ X + r := by linarith
    positivity
  refine iSup_Iic_le hRHS0 fun m hmn => ?_
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hzero : ∀ ω : Data d, |wErr ω m 0| ^ r = 0 := by
      intro ω
      rw [wErr_eq_zero_of_lt_two ω hm2, abs_zero, Real.zero_rpow (ne_of_gt hr0)]
    simp only [hzero, integral_zero]
    rw [Real.zero_rpow (one_div_ne_zero (ne_of_gt hr0))]
    exact hRHS0
  · obtain ⟨F, ξ, hFmono, hFle, hXimeas, hXiint, hXifin, hXitsum, hXicond, hXibd,
      hXisumm, hXiqv⟩ := Parking.Frozen.w_martingale d hd ν inferInstance m hm2
    have ha0 : 0 < greenIncrement d m := greenIncrement_pos hd hm2
    have haK : greenIncrement d m ≤ K := hKle m
    set ξ' : ℕ → Data d → ℝ := fun i => if i = 0 then 0 else ξ (i - 1) with hxidef
    have hxieq : ∀ i : ℕ, 1 ≤ i → ξ' i = ξ (i - 1) := fun i hi => by
      rw [hxidef]; exact if_neg (by omega)
    have hXiamb : ∀ j, Measurable (ξ j) := fun j => (hXimeas j).mono (hFle (j + 1)) le_rfl
    have hmeas' : ∀ i, Measurable[F i] (ξ' i) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have h0 : ξ' 0 = fun _ : Data d => (0 : ℝ) := by rw [hxidef]; exact if_pos rfl
        rw [h0]
        exact measurable_const
      · rw [hxieq i hi]
        have h1 : i - 1 + 1 = i := by omega
        have h2 := hXimeas (i - 1)
        rwa [h1] at h2
    have hint' : ∀ i, Integrable (ξ' i) (law d ν) := by
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have h0 : ξ' 0 = fun _ : Data d => (0 : ℝ) := by rw [hxidef]; exact if_pos rfl
        rw [h0]
        exact integrable_zero _ _ _
      · rw [hxieq i hi]; exact hXiint (i - 1)
    have hcond' : ∀ i : ℕ, 1 ≤ i →
        (law d ν)[ξ' i | F (i - 1)] =ᵐ[law d ν] 0 := by
      intro i hi
      rw [hxieq i hi]
      exact hXicond (i - 1)
    have hbd' : ∀ i : ℕ, 1 ≤ i → ∀ ω, |ξ' i ω| ≤ greenIncrement d m := by
      intro i hi ω
      rw [hxieq i hi]
      exact hXibd (i - 1) ω
    have hbern : ∀ k : ℕ,
        (∫ ω, |∑ i ∈ Finset.Icc 1 k, ξ' i ω| ^ r ∂(law d ν)) ^ (1 / r) ≤
          CB * (Real.sqrt r *
            (∫ ω, (∑ i ∈ Finset.Icc 1 k,
                ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν))
              ^ (1 / r)
            + r * greenIncrement d m) := fun k =>
      (hBern' (Data d) inferInstance (law d ν) inferInstance k F ξ' r (greenIncrement d m)
        hFmono hFle hmeas' hint' (fun i hi _ => hcond' i hi) hr2 ha0).1
        (fun i hi _ => hbd' i hi)
    -- the quadratic variation is below the bound over the box
    have hQV : ∀ k : ℕ, ∀ᵐ ω ∂(law d ν),
        0 ≤ (∑ i ∈ Finset.Icc 1 k,
            ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ∧
          (∑ i ∈ Finset.Icc 1 k,
            ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ≤ qvBound d n ω := by
      intro k
      have hnn : ∀ᵐ ω ∂(law d ν), ∀ j : ℕ,
          0 ≤ ((law d ν)[fun ω' => ξ j ω' ^ 2 | F j]) ω :=
        ae_all_iff.mpr fun j =>
          condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      filter_upwards [hnn, hXisumm, hXiqv] with ω hω1 hω2 hω3
      have hre : (∑ i ∈ Finset.Icc 1 k,
            ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω)
          = ∑ j ∈ Finset.range k, ((law d ν)[fun ω' => ξ j ω' ^ 2 | F j]) ω := by
        rw [← sum_Icc_shift (fun j => ((law d ν)[fun ω' => ξ j ω' ^ 2 | F j]) ω) k]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        rw [hxieq i hi1]
      rw [hre]
      refine ⟨Finset.sum_nonneg fun j _ => hω1 j, ?_⟩
      calc ∑ j ∈ Finset.range k, ((law d ν)[fun ω' => ξ j ω' ^ 2 | F j]) ω
          ≤ ∑' j, ((law d ν)[fun ω' => ξ j ω' ^ 2 | F j]) ω :=
            hω2.1.sum_le_tsum _ (fun j _ => hω1 j)
        _ = ∑ s ∈ Finset.Icc 1 (m - 1), ∑' y : Site d,
              ((A ω (s - 1) y : ℕ) : ℝ) * gamma d (m - s) y := hω3
        _ ≤ qvBound d n ω := qv_le_qvBound hd hmn ω
    -- the moment of the bound
    have hAle : ∀ k : ℕ,
        (∫ ω, (∑ i ∈ Finset.Icc 1 k,
            ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν))
          ≤ ∫ ω, qvBound d n ω ^ (r / 2) ∂(law d ν) := by
      intro k
      refine integral_mono_of_nonneg ?_ (integrable_qvBound_rpow hd ν hθ hexp hp1 n) ?_
      · filter_upwards [hQV k] with ω hω
        exact Real.rpow_nonneg hω.1 _
      · filter_upwards [hQV k] with ω hω
        exact Real.rpow_le_rpow hω.1 hω.2 (by linarith)
    -- the moment of the quadratic-variation bound
    set A : ℝ := ∫ ω, qvBound d n ω ^ (r / 2) ∂(law d ν) with hAdef
    have hA0 : 0 ≤ A := integral_nonneg fun ω => Real.rpow_nonneg (qvBound_nonneg hd n ω) _
    set T : ℝ := gammaTot d n with hTdef
    have hT0 : 0 ≤ T := gammaTot_nonneg hd n
    set Mu : ℝ := ∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ (r / 2) ∂(law d ν) with hMudef
    have hMu0 : 0 ≤ Mu := integral_nonneg fun ω => Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hAT : A ≤ T ^ (r / 2) * Mu := integral_qvBound_rpow_le hd ν hθ hexp hp1 n
    have hTCg : T ≤ Cg * kappa d n := gammaTot_le hd hgsum hn
    have hsqU : ∀ ω : Data d,
        (((U ω n 0 : ℕ) : ℝ) ^ (r / 2)) ^ (2 : ℕ) = ((U ω n 0 : ℕ) : ℝ) ^ r := by
      intro ω
      rw [rpow_sq (Nat.cast_nonneg _) (r / 2)]
      congr 1
      ring
    have hCS : Mu ^ (2 : ℕ) ≤ E := by
      have hint2 : Integrable
          (fun ω : Data d => (((U ω n 0 : ℕ) : ℝ) ^ (r / 2)) ^ (2 : ℕ)) (law d ν) := by
        simp only [hsqU]
        exact integrable_U_rpow hd ν hθ hexp hr1 n 0
      have hcs := sq_integral_le_integral_sq (law d ν)
        (fun ω => ((U ω n 0 : ℕ) : ℝ) ^ (r / 2))
        (integrable_U_rpow hd ν hθ hexp hp1 n 0) hint2
      simpa only [hsqU] using hcs
    have hArpow : A ^ (2 / r) ≤ T * D := by
      have h1 : A ^ (2 / r) ≤ (T ^ (r / 2) * Mu) ^ (2 / r) :=
        Real.rpow_le_rpow hA0 hAT (by positivity)
      have h2 : (T ^ (r / 2) * Mu) ^ (2 / r) = T * Mu ^ (2 / r) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hT0 _) hMu0, ← Real.rpow_mul hT0]
        have h3 : r / 2 * (2 / r) = 1 := by field_simp
        rw [h3, Real.rpow_one]
      have h4 : Mu ^ (2 / r) ≤ D := by
        have h5 : Mu ^ (2 / r) = (Mu ^ (2 : ℕ)) ^ (1 / r) := by
          rw [sq_rpow hMu0 (1 / r)]
          congr 1
          ring
        rw [h5, hDdef]
        exact Real.rpow_le_rpow (by positivity) hCS (by positivity)
      calc A ^ (2 / r) ≤ (T ^ (r / 2) * Mu) ^ (2 / r) := h1
        _ = T * Mu ^ (2 / r) := h2
        _ ≤ T * D := mul_le_mul_of_nonneg_left h4 hT0
    have hkD : (0 : ℝ) ≤ r * kappa d n * D :=
      mul_nonneg (mul_nonneg (le_of_lt hr0) (kappa_nonneg d n)) hD0
    have hsqrt : Real.sqrt r * A ^ (1 / r) ≤ Real.sqrt Cg * X := by
      have hL0 : 0 ≤ Real.sqrt r * A ^ (1 / r) := by positivity
      have hR0 : 0 ≤ Real.sqrt Cg * X := by positivity
      have hsq : (Real.sqrt r * A ^ (1 / r)) ^ (2 : ℕ) ≤ (Real.sqrt Cg * X) ^ (2 : ℕ) := by
        have hLsq : (Real.sqrt r * A ^ (1 / r)) ^ (2 : ℕ) = r * A ^ (2 / r) := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hr0), rpow_sq hA0 (1 / r)]
          have h21 : (2 : ℝ) * (1 / r) = 2 / r := by ring
          rw [h21]
        have hRsq : (Real.sqrt Cg * X) ^ (2 : ℕ) = Cg * (r * kappa d n * D) := by
          rw [mul_pow, Real.sq_sqrt (le_of_lt hCg), hXdef, Real.sq_sqrt hkD]
        rw [hLsq, hRsq]
        have h6 : r * A ^ (2 / r) ≤ r * (T * D) :=
          mul_le_mul_of_nonneg_left hArpow (le_of_lt hr0)
        have h7 : T * D ≤ Cg * kappa d n * D := mul_le_mul_of_nonneg_right hTCg hD0
        nlinarith
      calc Real.sqrt r * A ^ (1 / r)
          = Real.sqrt ((Real.sqrt r * A ^ (1 / r)) ^ (2 : ℕ)) := (Real.sqrt_sq hL0).symm
        _ ≤ Real.sqrt ((Real.sqrt Cg * X) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt Cg * X := Real.sqrt_sq hR0
    -- the partial sums of the martingale
    have hSk : ∀ (k : ℕ) (ω : Data d),
        (∑ i ∈ Finset.Icc 1 k, ξ' i ω) = ∑ j ∈ Finset.range k, ξ j ω := by
      intro k ω
      rw [← sum_Icc_shift (fun j => ξ j ω) k]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hxieq i (Finset.mem_Icc.mp hi).1]
    have hfint : ∀ k : ℕ,
        Integrable (fun ω : Data d => |∑ j ∈ Finset.range k, ξ j ω| ^ r) (law d ν) := by
      intro k
      have hmeas : Measurable fun ω : Data d => |∑ j ∈ Finset.range k, ξ j ω| ^ r :=
        (measurable_rpow_const (le_of_lt hr0)).comp
          ((Finset.measurable_sum _ fun j _ => hXiamb j).abs)
      refine Integrable.mono' (integrable_const (((k : ℝ) * greenIncrement d m) ^ r))
        hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) r)]
      refine Real.rpow_le_rpow (abs_nonneg _) ?_ (le_of_lt hr0)
      calc |∑ j ∈ Finset.range k, ξ j ω| ≤ ∑ j ∈ Finset.range k, |ξ j ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range k, greenIncrement d m :=
            Finset.sum_le_sum fun j _ => hXibd j ω
        _ = (k : ℝ) * greenIncrement d m := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hbound : ∀ k : ℕ,
        ∫ ω, |∑ j ∈ Finset.range k, ξ j ω| ^ r ∂(law d ν) ≤ RHS ^ r := by
      intro k
      have h1 := hbern k
      simp only [hSk k] at h1
      have hQ0 : (0 : ℝ) ≤ ∫ ω, (∑ i ∈ Finset.Icc 1 k,
          ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν) := by
        refine integral_nonneg_of_ae ?_
        filter_upwards [hQV k] with ω hω
        exact Real.rpow_nonneg hω.1 _
      have h2 : (∫ ω, (∑ i ∈ Finset.Icc 1 k,
          ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν)) ^ (1 / r)
          ≤ A ^ (1 / r) := Real.rpow_le_rpow hQ0 (hAle k) (by positivity)
      have h3 : (∫ ω, |∑ j ∈ Finset.range k, ξ j ω| ^ r ∂(law d ν)) ^ (1 / r) ≤ RHS := by
        refine le_trans h1 ?_
        rw [hRHSdef]
        have hs1 : Real.sqrt r * (∫ ω, (∑ i ∈ Finset.Icc 1 k,
            ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν)) ^ (1 / r)
            ≤ Real.sqrt Cg * X :=
          le_trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg r)) hsqrt
        have hs2 : r * greenIncrement d m ≤ r * K :=
          mul_le_mul_of_nonneg_left haK (le_of_lt hr0)
        have hCg0 : (0 : ℝ) ≤ Real.sqrt Cg := Real.sqrt_nonneg Cg
        have hfinal : Real.sqrt Cg * X + r * K
            ≤ (Real.sqrt Cg + K + 1) * (X + r) := by nlinarith
        calc CB * (Real.sqrt r * (∫ ω, (∑ i ∈ Finset.Icc 1 k,
              ((law d ν)[fun ω' => ξ' i ω' ^ 2 | F (i - 1)]) ω) ^ (r / 2) ∂(law d ν)) ^ (1 / r)
              + r * greenIncrement d m)
            ≤ CB * (Real.sqrt Cg * X + r * K) := by
              refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hCB)
              linarith
          _ ≤ CB * ((Real.sqrt Cg + K + 1) * (X + r)) :=
              mul_le_mul_of_nonneg_left hfinal (le_of_lt hCB)
          _ = CB * (Real.sqrt Cg + K + 1) * (X + r) := by ring
      have hI0 : (0 : ℝ) ≤ ∫ ω, |∑ j ∈ Finset.range k, ξ j ω| ^ r ∂(law d ν) :=
        integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r
      have h4 : ((∫ ω, |∑ j ∈ Finset.range k, ξ j ω| ^ r ∂(law d ν)) ^ (1 / r)) ^ r
          ≤ RHS ^ r := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) h3 (le_of_lt hr0)
      rwa [← Real.rpow_mul hI0, one_div, inv_mul_cancel₀ (ne_of_gt hr0), Real.rpow_one] at h4
    -- Fatou
    have hconv : ∀ᵐ ω ∂(law d ν),
        Filter.Tendsto (fun k => |∑ j ∈ Finset.range k, ξ j ω| ^ r) Filter.atTop
          (nhds (|wErr ω m 0| ^ r)) := by
      filter_upwards [hXifin, hXitsum] with ω hfin htsum
      obtain ⟨N, hN⟩ := hfin
      have hsummable : Summable (fun j => ξ j ω) :=
        summable_of_ne_finset_zero (s := Finset.range N) fun j hj =>
          hN j (by simpa using hj)
      have htend : Filter.Tendsto (fun k => ∑ j ∈ Finset.range k, ξ j ω) Filter.atTop
          (nhds (∑' j, ξ j ω)) := hsummable.hasSum.tendsto_sum_nat
      have hcont : Continuous fun x : ℝ => |x| ^ r :=
        (Real.continuous_rpow_const (le_of_lt hr0)).comp continuous_abs
      have hcomp := (hcont.tendsto (∑' j, ξ j ω)).comp htend
      rw [← htsum] at hcomp
      exact hcomp
    have hfinal : ∫ ω, |wErr ω m 0| ^ r ∂(law d ν) ≤ RHS ^ r :=
      integral_le_of_tendsto (fun k ω => Real.rpow_nonneg (abs_nonneg _) r)
        (integrable_abs_wErr_rpow hd ν hθ hexp hr1 m 0)
        (fun ω => Real.rpow_nonneg (abs_nonneg _) r) hconv hfint hbound
    have h2 : (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r) ≤ (RHS ^ r) ^ (1 / r) :=
      Real.rpow_le_rpow (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) r)
        hfinal (by positivity)
    rwa [← Real.rpow_mul hRHS0, mul_one_div, div_self (ne_of_gt hr0), Real.rpow_one] at h2

/-- The first display of `prop:w-moment` at a single law. -/
theorem exists_wErr_moment_const (hd : 1 ≤ d) (hBern : Parking.External.Bernstein)
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} (hθ : 0 < θ)
    (hexp : Integrable (fun k : ℤ => Real.exp (θ * max (k : ℝ) 0)) ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ r : ℝ, 2 ≤ r →
      (⨆ m ∈ Set.Iic n, (∫ ω, |wErr ω m 0| ^ r ∂(law d ν)) ^ (1 / r))
        ≤ C * (Real.sqrt (r * kappa d n *
            (∫ ω, ((U ω n 0 : ℕ) : ℝ) ^ r ∂(law d ν)) ^ (1 / r)) + r) := by
  obtain ⟨C, hC, h⟩ := exists_wErr_moment_const_uniform (d := d) hd hBern
  exact ⟨C, hC, h ν inferInstance θ hθ hexp⟩

end Parking

end