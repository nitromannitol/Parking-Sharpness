/-
The quadratic variation of the martingale of `lem:w-martingale`.

Conditionally on what the exploration has revealed by step `i`, the increment
there is the discrepancy of the truncated Green function at a known site under a
fresh instruction, so the conditional mean of its square is `Γ` at that site.
Summing over the steps groups the pairs into their rounds, and inside a round
into the sites, where the number of pairs at a site is exactly the number of
particles that stood there, so the sum is the lattice sum of `A_{s-1}Γ_{n-s}`.
-/
import Parking.Support.WCondExp

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Parking

open LatticeProb Finset

variable {d : ℕ}

/-! ### `Γ` as a walk average -/

theorem walkOp_eq_inv_sum (u : Site d → ℝ) (y : Site d) :
    walkOp u y = (2 * (d : ℝ))⁻¹ * ∑ z ∈ nbrFinset y, u z := by
  rw [walkOp, nbrSum, ← sum_nbrFinset_eq y u, div_eq_inv_mul]

/-- `Γ_m(y)` is the walk average of the squared discrepancy at `y`. -/
theorem gamma_eq_walkOp (m : ℕ) (y : Site d) :
    gamma d m y = walkOp (fun z => (green d m z - walkOp (green d m) y) ^ 2) y := by
  classical
  have hval : ∀ z ∈ nbrFinset y,
      kern d y z * (green d m z - walkOp (green d m) y) ^ 2
        = (2 * (d : ℝ))⁻¹ * (green d m z - walkOp (green d m) y) ^ 2 := by
    intro z hz
    rw [kern, if_pos hz]
  rw [gamma, Finset.sum_congr rfl hval, ← Finset.mul_sum,
    walkOp_eq_inv_sum (fun z => (green d m z - walkOp (green d m) y) ^ 2) y]

theorem gamma_le (hd : 1 ≤ d) (m : ℕ) (y : Site d) : gamma d m y ≤ (m : ℝ) ^ 2 := by
  classical
  have hterm : ∀ z ∈ nbrFinset y,
      kern d y z * (green d m z - walkOp (green d m) y) ^ 2 ≤ kern d y z * (m : ℝ) ^ 2 := by
    intro z _
    have hk : 0 ≤ kern d y z := by
      rw [kern]
      by_cases h : z ∈ nbrFinset y
      · rw [if_pos h]; positivity
      · rw [if_neg h]
    have h1 : 0 ≤ green d m z := green_nonneg _ _
    have h2 : green d m z ≤ (m : ℝ) := green_le hd _ _
    have h3 : 0 ≤ walkOp (green d m) y := walkOp_green_nonneg _ _
    have h4 : walkOp (green d m) y ≤ (m : ℝ) := walkOp_green_le hd _ _
    have hsq : (green d m z - walkOp (green d m) y) ^ 2 ≤ (m : ℝ) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_left hsq hk
  calc gamma d m y ≤ ∑ z ∈ nbrFinset y, kern d y z * (m : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (m : ℝ) ^ 2 := by rw [← Finset.sum_mul, sum_kern_eq_one hd y, one_mul]


/-! ### The conditional mean of the square -/

/-- The mean of the squared discrepancy under the instruction law is `Γ`. -/
theorem integral_wDisc_sq (i₀ : Fin d) (n : ℕ) (q : Site d × ℕ) (s : ℕ) :
    ∫ z, wDisc i₀ n q s z ^ 2 ∂(instructionLaw q.1) = gamma d (n - s) q.1 := by
  rw [integral_instructionLaw, gamma_eq_walkOp]
  exact walkOp_nbrProjVal i₀
    (fun w => (green d (n - s) w - walkOp (green d (n - s)) q.1) ^ 2) q.1

/-- `Γ` at the pair the exploration reads at step `i`. -/
def wGamma (i₀ : Fin d) (n i : ℕ) (ω : Data d) : ℝ :=
  gamma d (n - wRound i₀ n i ω) (wPair i₀ n i ω).1

theorem measurable_wGamma (i₀ : Fin d) (n i : ℕ) : Measurable (wGamma i₀ n i) :=
  measurable_of_determined (fun ω => (wRound i₀ n i ω, wPair i₀ n i ω))
    ((measurable_wRound i₀ n i).prodMk (measurable_wPair i₀ n i)) _
    fun ω ω' h => by
      have h1 : wRound i₀ n i ω = wRound i₀ n i ω' := congrArg Prod.fst h
      have h2 : wPair i₀ n i ω = wPair i₀ n i ω' := congrArg Prod.snd h
      rw [wGamma, wGamma, h1, h2]

theorem wGamma_wTrunc (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wGamma i₀ n i (wTrunc i₀ n i ω) = wGamma i₀ n i ω := by
  rw [wGamma, wGamma, wRound_wTrunc, wPair_wTrunc_self]

theorem measurable_wGamma_wFiltration (i₀ : Fin d) (n i : ℕ) :
    Measurable[wFiltration i₀ n i] (wGamma i₀ n i) := by
  have hself : Measurable[wFiltration i₀ n i,
      inferInstanceAs (MeasurableSpace (Data d))] (wTrunc i₀ n i) :=
    measurable_iff_comap_le.mpr le_rfl
  have hcomp : Measurable[wFiltration i₀ n i]
      (fun ω => wGamma i₀ n i (wTrunc i₀ n i ω)) :=
    (measurable_wGamma i₀ n i).comp hself
  simpa only [wGamma_wTrunc] using hcomp

theorem wGamma_nonneg (i₀ : Fin d) (n i : ℕ) (ω : Data d) : 0 ≤ wGamma i₀ n i ω :=
  gamma_nonneg _ _ _

theorem wGamma_le (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (ω : Data d) :
    wGamma i₀ n i ω ≤ (n : ℝ) ^ 2 := by
  refine le_trans (gamma_le hd _ _) ?_
  have h : ((n - wRound i₀ n i ω : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (wRound i₀ n i ω)
  have h0 : (0 : ℝ) ≤ ((n - wRound i₀ n i ω : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem integrable_wGamma (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n i : ℕ) : Integrable (wGamma i₀ n i) (law d ν) := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  refine (integrable_const ((n : ℝ) ^ 2)).mono'
    (measurable_wGamma i₀ n i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (wGamma_nonneg i₀ n i ω)]
  exact wGamma_le hd i₀ n i ω

theorem integrable_wXi_sq (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    Integrable (fun ω => wXi i₀ n i ω ^ 2) (law d ν) := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  refine (integrable_const (greenIncrement d n ^ 2)).mono'
    ((measurable_wXi i₀ n i).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := abs_wXi_le hd i₀ n hn i ω
  have h2 : (0 : ℝ) ≤ |wXi i₀ n i ω| := abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  nlinarith

/-- **On a piece of the sigma-algebra of step `i` the square of the increment
and `Γ` at the pair have the same integral.** -/
theorem setIntegral_wXi_sq_piece (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n i : ℕ) (q : Site d × ℕ) (s : ℕ)
    {B : Set (Data d)} (hB : MeasurableSet B) :
    ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wXi i₀ n i ω ^ 2 ∂(law d ν)
      = ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wGamma i₀ n i ω ∂(law d ν) := by
  have hEm : MeasurableSet ((wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s) := by
    refine MeasurableSet.inter ((measurable_wTrunc i₀ n i) hB) ?_
    exact wFiltration_le i₀ n i _ (measurableSet_wEvent i₀ n i q s)
  have hleft : ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wXi i₀ n i ω ^ 2 ∂(law d ν)
      = ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s,
          wDisc i₀ n q s (ω.2.1 q) ^ 2 ∂(law d ν) := by
    refine setIntegral_congr_fun hEm fun ω hω => ?_
    rw [wXi_eq_wDisc hd i₀ n i q s hω.2]
  have hright : ∫ ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s, wGamma i₀ n i ω ∂(law d ν)
      = ∫ _ω in (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i q s,
          gamma d (n - s) q.1 ∂(law d ν) := by
    refine setIntegral_congr_fun hEm fun ω hω => ?_
    rw [wGamma, hω.2.1, hω.2.2]
  have hbound : ∀ z : Site d, ‖wDisc i₀ n q s z ^ 2‖ ≤ (2 * (n : ℝ)) ^ 2 := by
    intro z
    have h1 := abs_wDisc_le hd i₀ n q s z
    have h2 : (0 : ℝ) ≤ |wDisc i₀ n q s z| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    nlinarith
  rw [hleft, hright, setIntegral_const, smul_eq_mul, measureReal_def,
    setIntegral_eval_piece hd i₀ ν n i q s hB (fun z => wDisc i₀ n q s z ^ 2)
      ((2 * (n : ℝ)) ^ 2) hbound,
    integral_wDisc_sq i₀ n q s]


/-- **The set integral of the square of the increment over any set of the
sigma-algebra of step `i` is that of `Γ` at the pair.** -/
theorem setIntegral_wXi_sq_eq (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] (n : ℕ) (hn : 1 ≤ n) (i : ℕ) {A : Set (Data d)}
    (hA : MeasurableSet[wFiltration i₀ n i] A) :
    ∫ ω in A, wXi i₀ n i ω ^ 2 ∂(law d ν) = ∫ ω in A, wGamma i₀ n i ω ∂(law d ν) := by
  classical
  obtain ⟨B, hB, rfl⟩ := hA
  set κ : (Site d × ℕ) × ℕ → Set (Data d) := fun c =>
    (wTrunc i₀ n i ⁻¹' B) ∩ wEvent i₀ n i c.1 c.2 with hκ
  have hmeas : ∀ c, MeasurableSet (κ c) := fun c => by
    refine MeasurableSet.inter ((measurable_wTrunc i₀ n i) hB) ?_
    exact wFiltration_le i₀ n i _ (measurableSet_wEvent i₀ n i c.1 c.2)
  have hdisj : Pairwise (Function.onFun Disjoint κ) := by
    intro c c' hcc
    refine Set.disjoint_left.mpr fun ω hω hω' => ?_
    have h1 : wPair i₀ n i ω = c.1 := hω.2.1
    have h2 : wRound i₀ n i ω = c.2 := hω.2.2
    have h1' : wPair i₀ n i ω = c'.1 := hω'.2.1
    have h2' : wRound i₀ n i ω = c'.2 := hω'.2.2
    exact hcc (Prod.ext (h1 ▸ h1') (h2 ▸ h2'))
  have hunion : ⋃ c, κ c = wTrunc i₀ n i ⁻¹' B := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun c => Set.inter_subset_left) ?_
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨(wPair i₀ n i ω, wRound i₀ n i ω), hω, rfl, rfl⟩
  have hint1 : IntegrableOn (fun ω => wXi i₀ n i ω ^ 2) (⋃ c, κ c) (law d ν) :=
    (integrable_wXi_sq hd i₀ ν n hn i).integrableOn
  have hint2 : IntegrableOn (wGamma i₀ n i) (⋃ c, κ c) (law d ν) :=
    (integrable_wGamma hd i₀ ν n i).integrableOn
  rw [← hunion, integral_iUnion hmeas hdisj hint1, integral_iUnion hmeas hdisj hint2]
  refine tsum_congr fun c => ?_
  exact setIntegral_wXi_sq_piece hd i₀ ν n i c.1 c.2 hB

/-- **The conditional mean of the square of the increment is `Γ` at the pair the
exploration reads.** -/
theorem condExp_wXi_sq (hd : 1 ≤ d) (i₀ : Fin d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (i : ℕ) :
    (law d ν)[fun ω => wXi i₀ n i ω ^ 2 | wFiltration i₀ n i]
      =ᵐ[law d ν] wGamma i₀ n i := by
  haveI := stackLaw_isProbability (d := d) hd
  haveI := rankLaw_isProbability d
  haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
    unfold LatticeProb.iidLaw; infer_instance
  haveI : IsProbabilityMeasure (law d ν) := by unfold law; infer_instance
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq (wFiltration_le i₀ n i)
    (integrable_wXi_sq hd i₀ ν n hn i)
    (fun s _ _ => (integrable_wGamma hd i₀ ν n i).integrableOn)
    (fun s hs _ => (setIntegral_wXi_sq_eq hd i₀ ν n hn i hs).symm)
    (measurable_wGamma_wFiltration i₀ n i).aestronglyMeasurable).symm


/-! ### The sum of the conditional variances -/

theorem gamma_eq_zero_of_notMem_box {m : ℕ} {y : Site d}
    (h : y ∉ boxFinset (0 : Site d) m) : gamma d m y = 0 := by
  refine gamma_eq_zero_of_lt (lt_of_lt_of_le ?_ (supNorm_le_graphNorm y))
  by_contra hc
  exact h (mem_boxFinset_zero_iff.mpr (by omega))

theorem gamma_padSite (hd : 1 ≤ d) (n : ℕ) : gamma d n (padSite d n) = 0 := by
  refine gamma_eq_zero_of_notMem_box (padSite_notMem_box hd n n ?_)
  have h : n - 1 ≤ n := Nat.sub_le n 1
  simp only [blockRad]
  omega

/-- The sum of a function of the SITE over a block is the sum over the box,
weighted by the number of instructions the round reads at each site. -/
theorem sum_blockAt_site (ω : Data d) (R s : ℕ) (f : Site d → ℝ) :
    ∑ q ∈ blockAt ω R s, f q.1
      = ∑ y ∈ boxFinset (0 : Site d) R, ((U ω s y - U ω (s - 1) y : ℕ) : ℝ) * f y := by
  classical
  rw [blockAt, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_image (fun a _ b _ h => (Prod.mk.injEq _ _ _ _ ▸ h).2)]
    show ∑ _j ∈ Finset.Ico (U ω (s - 1) y) (U ω s y), f y
      = ((U ω s y - U ω (s - 1) y : ℕ) : ℝ) * f y
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  · intro y _ y' _ hyy'
    refine Finset.disjoint_left.mpr fun q hq hq' => ?_
    rw [Finset.mem_image] at hq hq'
    obtain ⟨j, _, rfl⟩ := hq
    obtain ⟨j', _, h⟩ := hq'
    exact hyy' (congrArg Prod.fst h).symm

theorem U_sub_eq_A (ω : Data d) {s : ℕ} (hs : 1 ≤ s) (y : Site d) :
    U ω s y - U ω (s - 1) y = A ω (s - 1) y := by
  have h := U_succ ω (s - 1) y
  rw [Nat.sub_add_cancel hs] at h
  omega

/-- **The lattice sum of one round, over the box the exploration reads it in.** -/
theorem sum_blockAt_gamma (ω : Data d) {n s : ℕ} (hs : 1 ≤ s) :
    ∑ q ∈ blockAt ω (blockRad n s) s, gamma d (n - s) q.1
      = ∑' y : Site d, (A ω (s - 1) y : ℝ) * gamma d (n - s) y := by
  classical
  have hzero : ∀ y : Site d, y ∉ boxFinset (0 : Site d) (blockRad n s) →
      (A ω (s - 1) y : ℝ) * gamma d (n - s) y = 0 := by
    intro y hy
    have : gamma d (n - s) y = 0 :=
      gamma_eq_zero_of_notMem_box fun hc => hy (boxFinset_mono (le_blockRad n s) hc)
    rw [this, mul_zero]
  rw [tsum_eq_sum (s := boxFinset (0 : Site d) (blockRad n s)) hzero,
    sum_blockAt_site ω (blockRad n s) s (gamma d (n - s))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [U_sub_eq_A ω hs y]

theorem summable_A_gamma (ω : Data d) (n s : ℕ) :
    Summable fun y : Site d => (A ω (s - 1) y : ℝ) * gamma d (n - s) y := by
  classical
  refine summable_of_ne_finset_zero (s := boxFinset (0 : Site d) (n - s)) fun y hy => ?_
  rw [gamma_eq_zero_of_notMem_box hy, mul_zero]

/-- **The sum of the conditional variances**, pathwise on the realizations whose
instructions are neighbours of their site. -/
theorem tsum_wGamma_eq (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (ω : Data d)
    (hstep : ∀ q : Site d × ℕ, ω.2.1 q ∈ nbrFinset q.1) :
    ∑' i : ℕ, wGamma i₀ n i ω
      = ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Site d,
          (A ω (s - 1) y : ℝ) * gamma d (n - s) y := by
  classical
  have hproj : wProj i₀ ω = ω := by
    have hstack : nbrProj i₀ ω.2.1 = ω.2.1 := by
      funext q
      rw [nbrProj, if_pos (hstep q)]
    show ((ω.1, nbrProj i₀ ω.2.1, ω.2.2) : Data d) = ω
    rw [hstack]
  set L := blockPrefix ω n (n - 1) with hL
  set M := L.map (fun q => gamma d (n - roundOf ω q) q.1) with hM
  have hval : ∀ i, wGamma i₀ n i ω = M.getD i 0 := by
    intro i
    have hpair : wPair i₀ n i ω = L.getD i (padSite d n, i) := by
      rw [hL]
      show (blockPrefix (wProj i₀ ω) n (n - 1)).getD i (padSite d n, i)
        = (blockPrefix ω n (n - 1)).getD i (padSite d n, i)
      rw [hproj]
    by_cases hi : i < L.length
    · have hMlen : i < (L.map (fun q => gamma d (n - roundOf ω q) q.1)).length := by
        rw [List.length_map]; exact hi
      have hround : wRound i₀ n i ω = roundOf ω (wPair i₀ n i ω) := by
        rw [wRound, if_pos (by rw [hproj]; exact hi), hproj]
      have hgetL : wPair i₀ n i ω = L[i]'hi := by
        rw [hpair, List.getD_eq_getElem _ _ hi]
      rw [wGamma, hround, hgetL, hM, List.getD_eq_getElem _ _ hMlen, List.getElem_map]
    · have hMlen : (L.map (fun q => gamma d (n - roundOf ω q) q.1)).length ≤ i := by
        rw [List.length_map]; exact Nat.le_of_not_lt hi
      have hround : wRound i₀ n i ω = 0 := by
        rw [wRound, if_neg (by rw [hproj]; exact hi)]
      have hpad : wPair i₀ n i ω = (padSite d n, i) := by
        rw [hpair, List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
      rw [wGamma, hround, hpad, Nat.sub_zero, gamma_padSite hd n, hM,
        List.getD_eq_default _ _ hMlen]
  calc ∑' i : ℕ, wGamma i₀ n i ω = ∑' i : ℕ, M.getD i 0 := by simp only [hval]
    _ = M.sum := tsum_getD_eq_sum M
    _ = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ q ∈ blockAt ω (blockRad n s) s,
          gamma d (n - roundOf ω q) q.1 := sum_map_blockPrefix ω n (n - 1) _
    _ = ∑ s ∈ Finset.Icc 1 (n - 1), ∑ q ∈ blockAt ω (blockRad n s) s,
          gamma d (n - s) q.1 := by
        refine Finset.sum_congr rfl fun s hs => ?_
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [roundOf_eq_of_mem_blockAt (Finset.mem_Icc.mp hs).1 hq]
    _ = ∑ s ∈ Finset.Icc 1 (n - 1), ∑' y : Site d,
          (A ω (s - 1) y : ℝ) * gamma d (n - s) y := by
        refine Finset.sum_congr rfl fun s hs => ?_
        exact sum_blockAt_gamma ω (Finset.mem_Icc.mp hs).1


theorem wGamma_eq_zero_of_le (hd : 1 ≤ d) (i₀ : Fin d) (n i : ℕ) (ω : Data d)
    (h : (blockPrefix (wProj i₀ ω) n (n - 1)).length ≤ i) : wGamma i₀ n i ω = 0 := by
  have hround : wRound i₀ n i ω = 0 := by rw [wRound, if_neg (by omega)]
  have hpad : wPair i₀ n i ω = (padSite d n, i) := by
    show (blockPrefix (wProj i₀ ω) n (n - 1)).getD i (padSite d n, i) = (padSite d n, i)
    rw [List.getD_eq_default _ _ h]
  rw [wGamma, hround, hpad, Nat.sub_zero, gamma_padSite hd n]

theorem summable_wGamma (hd : 1 ≤ d) (i₀ : Fin d) (n : ℕ) (ω : Data d) :
    Summable fun i => wGamma i₀ n i ω :=
  summable_of_ne_finset_zero
    (s := Finset.range (blockPrefix (wProj i₀ ω) n (n - 1)).length)
    fun i hi => wGamma_eq_zero_of_le hd i₀ n i ω
      (Nat.le_of_not_lt (by simpa using hi))


/-! ### The predictable quadratic variation against the odometer -/

theorem sum_A_Icc (ω : Data d) (k : ℕ) (y : Site d) :
    ∑ s ∈ Finset.Icc 1 k, A ω (s - 1) y = U ω k y := by
  induction k with
  | zero =>
      have hempty : ∑ s ∈ Finset.Icc 1 0, A ω (s - 1) y = 0 := by simp
      rw [hempty]
      rfl
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, U_eq_sum_A, U_eq_sum_A,
        Finset.sum_range_succ, Nat.add_sub_cancel]

/-- Every `Γ_m(y)` with `m ≤ n` is below the supremum of `lem:gamma-sum`. -/
theorem le_iSup_gamma_Iic (hd : 1 ≤ d) {n m : ℕ} (hm : m ∈ Set.Iic n) (y : Site d) :
    gamma d m y ≤ ⨆ j ∈ Set.Iic n, gamma d j y := by
  have hbdd : ∀ j : ℕ, (⨆ _ : j ∈ Set.Iic n, gamma d j y) ≤ (n : ℝ) ^ 2 := by
    intro j
    by_cases h : j ∈ Set.Iic n
    · rw [ciSup_pos h]
      refine le_trans (gamma_le hd j y) ?_
      have hj : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
      nlinarith
    · rw [ciSup_neg h, Real.sSup_empty]
      positivity
  have hb : BddAbove (Set.range fun j : ℕ => ⨆ _ : j ∈ Set.Iic n, gamma d j y) :=
    ⟨(n : ℝ) ^ 2, by rintro x ⟨j, rfl⟩; exact hbdd j⟩
  calc gamma d m y = ⨆ _ : m ∈ Set.Iic n, gamma d m y :=
        (ciSup_pos (f := fun _ : m ∈ Set.Iic n => gamma d m y) hm).symm
    _ ≤ ⨆ j : ℕ, ⨆ _ : j ∈ Set.Iic n, gamma d j y := le_ciSup hb m

theorem iSup_gamma_Iic_nonneg (hd : 1 ≤ d) (n : ℕ) (y : Site d) :
    0 ≤ ⨆ j ∈ Set.Iic n, gamma d j y :=
  le_trans (gamma_nonneg d 0 y) (le_iSup_gamma_Iic hd (Set.mem_Iic.mpr (Nat.zero_le n)) y)

/-- **The predictable quadratic variation at one site is at most the odometer
there against the largest `Γ`.**  This is the first display of the proof of
`prop:w-moment`, before the lattice sum is taken. -/
theorem qv_le_pointwise (hd : 1 ≤ d) (n : ℕ) (ω : Data d) (y : Site d) :
    ∑ s ∈ Finset.Icc 1 (n - 1), (A ω (s - 1) y : ℝ) * gamma d (n - s) y
      ≤ (⨆ j ∈ Set.Iic n, gamma d j y) * (U ω n y : ℝ) := by
  set S : ℝ := ⨆ j ∈ Set.Iic n, gamma d j y with hS
  have hS0 : 0 ≤ S := iSup_gamma_Iic_nonneg hd n y
  have hstep : ∀ s ∈ Finset.Icc 1 (n - 1),
      (A ω (s - 1) y : ℝ) * gamma d (n - s) y ≤ (A ω (s - 1) y : ℝ) * S :=
    fun s _ => mul_le_mul_of_nonneg_left
      (le_iSup_gamma_Iic hd (Set.mem_Iic.mpr (Nat.sub_le n s)) y) (Nat.cast_nonneg _)
  have hmono : U ω (n - 1) y ≤ U ω n y :=
    LatticeProb.particleOdometer_mono (toDriver ω) y (Nat.sub_le n 1)
  have hcast : ((U ω (n - 1) y : ℕ) : ℝ) ≤ ((U ω n y : ℕ) : ℝ) := by exact_mod_cast hmono
  calc ∑ s ∈ Finset.Icc 1 (n - 1), (A ω (s - 1) y : ℝ) * gamma d (n - s) y
      ≤ ∑ s ∈ Finset.Icc 1 (n - 1), (A ω (s - 1) y : ℝ) * S := Finset.sum_le_sum hstep
    _ = (∑ s ∈ Finset.Icc 1 (n - 1), (A ω (s - 1) y : ℝ)) * S := (Finset.sum_mul _ _ _).symm
    _ = ((U ω (n - 1) y : ℕ) : ℝ) * S := by
        rw [← Nat.cast_sum, sum_A_Icc]
    _ ≤ ((U ω n y : ℕ) : ℝ) * S := mul_le_mul_of_nonneg_right hcast hS0
    _ = S * (U ω n y : ℝ) := mul_comm _ _

end Parking

end
