import Parking.External.CriticalScaleLowerTail
import Parking.Support.NearestCriticalNormalization
import Parking.External.VarianceScale
import LatticeProb.Walk.ExteriorDirichlet
import Parking.Support.MeanPos
import Sandpile.Support.CriticalAssembly

/-!
# The critical-scale lower tail estimate, proved

Proves `Parking.External.criticalScaleLowerTail`, the critical-scale lower tail estimate of
Bou-Rabee and Panagiotis cited as an external input in
`Parking/External/CriticalScaleLowerTail.lean` (`sandpile.tex:1696-1720`,
`parking.tex:1822-1848`), outright from that statement's own `VarianceScale` and
`MultivariateBerryEsseen` hypotheses. The route runs the floor-free linear evolution
`cslt_linear` against the Green function of the kernel and closes with the centred mass
law's lower tail.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology

/-! The floor-free evolution used in the deterministic part of the source proof. -/

/-- The floor-free linear evolution `η + P(cslt_linear η n)`: the odometer recursion
`Parking.u` with the `max 0` truncation removed. -/
def Parking.External.cslt_linear {d : ℕ} (η : Parking.Site d → ℝ) :
    ℕ → Parking.Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => η x + Parking.walkOp (cslt_linear η n) x

/-- The floor-free evolution never exceeds the true odometer, `cslt_linear η n x ≤
Parking.u η n x`, by induction using monotonicity of `walkOp` and `a ≤ max 0 a`. -/
theorem Parking.External.cslt_linear_le_u {d : ℕ} (hd : 1 ≤ d)
    (η : Parking.Site d → ℝ) (n : ℕ) (x : Parking.Site d) :
    cslt_linear η n x ≤ Parking.u η n x := by
  induction n generalizing x with
  | zero => simp [cslt_linear, Parking.u]
  | succ n ih =>
      rw [cslt_linear, Parking.u]
      calc
        η x + Parking.walkOp (cslt_linear η n) x ≤
            η x + Parking.walkOp (Parking.u η n) x :=
          add_le_add (le_refl _) (Parking.walkOp_mono hd (fun y => ih y) x)
        _ ≤ max 0 (η x + Parking.walkOp (Parking.u η n) x) :=
          le_max_right _ _

/-- For `n ≤ t`, the small-value event for the true odometer at time `t` is contained in the
corresponding event for the floor-free evolution at time `n`, via `cslt_linear_le_u` and the
monotonicity of `Parking.u` in time. -/
theorem Parking.External.cslt_lower_tail_subset {d : ℕ} (hd : 1 ≤ d)
    {n t : ℕ} (hnt : n ≤ t) {h : ℝ} :
    {η : Parking.Site d → ℝ | Parking.u η t 0 ≤ h} ⊆
      {η : Parking.Site d → ℝ | cslt_linear η n 0 ≤ h} := by
  intro η hη
  exact (cslt_linear_le_u hd η n 0).trans
    ((Parking.u_monotone_time hd η 0 hnt).trans hη)

/-- `walkOp` commutes with an infinite sum `∑' y, F y ·` when only the finitely many `y ∈ s`
contribute a nonzero value at either neighbor of `x` in each direction. -/
theorem Parking.External.cslt_walkOp_tsum {d : ℕ} (s : Finset (Parking.Site d))
    (F : Parking.Site d → Parking.Site d → ℝ)
    (x : Parking.Site d)
    (hF : ∀ y ∉ s, ∀ i : Fin d,
      F y (x + unit i) = 0 ∧ F y (x - unit i) = 0) :
    Parking.walkOp (fun z => ∑' y, F y z) x =
      ∑' y, Parking.walkOp (F y) x := by
  classical
  have htsumplus : ∀ i : Fin d, (∑' y, F y (x + unit i)) =
      ∑ y ∈ s, F y (x + unit i) := by
    intro i
    exact tsum_eq_sum fun y hy => (hF y hy i).1
  have htsumminus : ∀ i : Fin d, (∑' y, F y (x - unit i)) =
      ∑ y ∈ s, F y (x - unit i) := by
    intro i
    exact tsum_eq_sum fun y hy => (hF y hy i).2
  have hout : ∀ y ∉ s, Parking.walkOp (F y) x = 0 := by
    intro y hy
    rw [Parking.walkOp, LatticeProb.nbrSum]
    have hz : (∑ i : Fin d, (F y (x + unit i) + F y (x - unit i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [(hF y hy i).1, (hF y hy i).2, zero_add]
    rw [hz, zero_div]
  have hright : (∑' y, Parking.walkOp (F y) x) =
      ∑ y ∈ s, Parking.walkOp (F y) x :=
    tsum_eq_sum hout
  rw [hright, Parking.walkOp, LatticeProb.nbrSum]
  simp_rw [htsumplus, htsumminus]
  simp_rw [Parking.walkOp, LatticeProb.nbrSum]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib]
  apply congrArg (fun z : ℝ => z / (2 * (d : ℝ)))
  congr 1
  · exact Finset.sum_comm
  · exact Finset.sum_comm

/-- The `n`-step heat kernel vanishes off the box `LatticeProb.boxFinset x n`: the finite
propagation of the simple random walk in `n` steps. -/
theorem Parking.External.cslt_heat_zero_of_not_mem {d n : ℕ}
    {x y : Parking.Site d} (hy : y ∉ LatticeProb.boxFinset x n) :
    Parking.CriticalScale.heatKernel d n x y = 0 := by
  change LatticeProb.LocalCLT.heatKernel d n x y = 0
  rw [LatticeProb.heatKernel_eq_srwHeat]
  apply LatticeProb.srwHeat_eq_zero_of_notMem_box
  intro hxy
  apply hy
  rw [LatticeProb.mem_boxFinset_iff] at hxy ⊢
  intro i
  have hi := hxy i
  simpa [sub_zero, abs_sub_comm] using hi

/-- The truncated Green function `greenTime d n x ·` vanishes off `LatticeProb.boxFinset x n`,
since every summand `heatKernel d k x ·` with `k ≤ n` already vanishes there by
`cslt_heat_zero_of_not_mem`. -/
theorem Parking.External.cslt_green_zero_of_not_mem {d n : ℕ}
    {x y : Parking.Site d} (hy : y ∉ LatticeProb.boxFinset x n) :
    Parking.CriticalScale.greenTime d n x y = 0 := by
  change (∑ k ∈ Finset.range n,
      LatticeProb.LocalCLT.heatKernel d k x y) = 0
  apply Finset.sum_eq_zero
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
  have hyk : y ∉ LatticeProb.boxFinset x k := by
    intro hyk
    exact hy (LatticeProb.boxFinset_mono hkn hyk)
  exact cslt_heat_zero_of_not_mem hyk

/-- The Green function's one-step recursion, `greenTime d (n + 1) x y = greenTime d n x y +
heatKernel d n x y`, splitting off the last term of the defining sum. -/
theorem Parking.External.cslt_green_succ (d n : ℕ) (x y : Parking.Site d) :
    Parking.CriticalScale.greenTime d (n + 1) x y =
      Parking.CriticalScale.greenTime d n x y +
        Parking.CriticalScale.heatKernel d n x y := by
  change (∑ k ∈ Finset.range (n + 1), LatticeProb.LocalCLT.heatKernel d k x y) =
    (∑ k ∈ Finset.range n, LatticeProb.LocalCLT.heatKernel d k x y) +
      LatticeProb.LocalCLT.heatKernel d n x y
  rw [Finset.sum_range_succ]

/-- The Green function's own transport identity, `walkOp (greenTime d n · y) x =
greenTime d (n + 1) x y - heatKernel d 0 x y`, from re-indexing its defining sum against an
eventually-zero kernel. -/
theorem Parking.External.cslt_green_walk {d n : ℕ} (x y : Parking.Site d) :
    Parking.walkOp (fun z => Parking.CriticalScale.greenTime d n z y) x =
      Parking.CriticalScale.greenTime d (n + 1) x y -
        Parking.CriticalScale.heatKernel d 0 x y := by
  let F : ℕ → Parking.Site d → ℝ := fun k z =>
    if k < n then Parking.CriticalScale.heatKernel d k z y else 0
  have hsum : ∀ z : Parking.Site d, Summable (fun k => F k z) := by
    intro z
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    simp only [F]
    rw [if_neg]
    exact Nat.not_lt_of_ge (Nat.le_of_not_gt (by simpa using hk))
  have hF : ∀ z : Parking.Site d, (∑' k, F k z) =
      Parking.CriticalScale.greenTime d n z y := by
    intro z
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      simp only [F]
      rw [if_neg]
      exact Nat.not_lt_of_ge (Nat.le_of_not_gt (by simpa using hk)))]
    change (∑ k ∈ Finset.range n, if k < n then
        LatticeProb.LocalCLT.heatKernel d k z y else 0) =
      ∑ k ∈ Finset.range n, LatticeProb.LocalCLT.heatKernel d k z y
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  have hstep : ∀ k : ℕ,
      Parking.walkOp (F k) x =
        if k < n then Parking.CriticalScale.heatKernel d (k + 1) x y else 0 := by
    intro k
    by_cases hk : k < n
    · simp only [F, if_pos hk]
      change Parking.walkOp (fun z =>
        LatticeProb.LocalCLT.heatKernel d k z y) x =
          LatticeProb.LocalCLT.heatKernel d (k + 1) x y
      rfl
    · simp only [F, if_neg hk]
      simp [Parking.walkOp, LatticeProb.nbrSum]
  rw [show (fun z => Parking.CriticalScale.greenTime d n z y) =
      (fun z => ∑' k, F k z) by funext z; exact (hF z).symm]
  rw [LatticeProb.walkOp_tsum hsum x]
  have hfinite : (∑' k, (if k < n then
      Parking.CriticalScale.heatKernel d (k + 1) x y else 0)) =
      ∑ k ∈ Finset.range n, Parking.CriticalScale.heatKernel d (k + 1) x y := by
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      rw [if_neg]
      exact Nat.not_lt_of_ge (Nat.le_of_not_gt (by simpa using hk)))]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  rw [tsum_congr hstep, hfinite]
  change (∑ k ∈ Finset.range n, LatticeProb.LocalCLT.heatKernel d (k + 1) x y) =
    (∑ k ∈ Finset.range (n + 1), LatticeProb.LocalCLT.heatKernel d k x y) -
      LatticeProb.LocalCLT.heatKernel d 0 x y
  rw [Finset.sum_range_succ']
  ring

/-- The Green-function representation of the floor-free evolution,
`cslt_linear η n x = ∑' y, greenTime d n x y * η y`, by induction using `cslt_green_walk`
and the vanishing of the truncated kernel off a finite box. -/
theorem Parking.External.cslt_linear_green {d : ℕ} (η : Parking.Site d → ℝ)
    (n : ℕ) (x : Parking.Site d) :
    cslt_linear η n x =
      ∑' y, Parking.CriticalScale.greenTime d n x y * η y := by
  induction n generalizing x with
  | zero => simp [cslt_linear, LatticeProb.greenTime]
  | succ n ih =>
      have hplus : ∀ i : Fin d,
          x + unit i ∈ LatticeProb.boxFinset x 1 := by
        intro i
        rw [LatticeProb.mem_boxFinset_iff]
        intro j
        by_cases hji : j = i
        · subst j
          simp [unit]
        · simp [unit, hji]
      have hminus : ∀ i : Fin d,
          x - unit i ∈ LatticeProb.boxFinset x 1 := by
        intro i
        rw [LatticeProb.mem_boxFinset_iff]
        intro j
        by_cases hji : j = i
        · subst j
          simp [unit]
        · simp [unit, hji]
      have hcomm :
          Parking.walkOp (fun z => ∑' y,
              Parking.CriticalScale.greenTime d n z y * η y) x =
            ∑' y, Parking.walkOp (fun z =>
              Parking.CriticalScale.greenTime d n z y * η y) x := by
        apply cslt_walkOp_tsum (s := LatticeProb.boxFinset x (n + 1))
          (F := fun y z => Parking.CriticalScale.greenTime d n z y * η y) x
        intro y hy i
        constructor
        · have hy' : y ∉ LatticeProb.boxFinset (x + unit i) n := by
            intro hy'
            apply hy
            simpa [Nat.add_comm] using
              (LatticeProb.mem_boxFinset_add (hplus i) hy')
          rw [cslt_green_zero_of_not_mem hy', zero_mul]
        · have hy' : y ∉ LatticeProb.boxFinset (x - unit i) n := by
            intro hy'
            apply hy
            simpa [Nat.add_comm] using
              (LatticeProb.mem_boxFinset_add (hminus i) hy')
          rw [cslt_green_zero_of_not_mem hy', zero_mul]
      have hnext : Summable (fun y =>
          Parking.CriticalScale.greenTime d (n + 1) x y * η y) := by
        apply summable_of_ne_finset_zero (s := LatticeProb.boxFinset x (n + 1))
        intro y hy
        rw [cslt_green_zero_of_not_mem hy, zero_mul]
      have hzero : Summable (fun y =>
          Parking.CriticalScale.heatKernel d 0 x y * η y) := by
        apply summable_of_ne_finset_zero (s := LatticeProb.boxFinset x (n + 1))
        intro y hy
        have hy0 : y ∉ LatticeProb.boxFinset x 0 := by
          intro hy0
          apply hy
          exact LatticeProb.boxFinset_mono (Nat.zero_le _) hy0
        rw [cslt_heat_zero_of_not_mem hy0, zero_mul]
      have hzero_sum : (∑' y,
          Parking.CriticalScale.heatKernel d 0 x y * η y) = η x := by
        change (∑' y, (if x = y then (1 : ℝ) else 0) * η y) = η x
        simp only [ite_mul, one_mul, zero_mul]
        rw [show (fun y : Parking.Site d => if x = y then η y else 0) =
            (fun y => if y = x then η y else 0) by
              funext y; by_cases hxy : x = y <;> simp [hxy, eq_comm]]
        simp
      have hwalk : ∀ y : Parking.Site d,
          Parking.walkOp (fun z =>
              Parking.CriticalScale.greenTime d n z y * η y) x =
            Parking.CriticalScale.greenTime d (n + 1) x y * η y -
              Parking.CriticalScale.heatKernel d 0 x y * η y := by
        intro y
        rw [LatticeProb.walkOp_mul_const, cslt_green_walk]
        ring
      calc
        cslt_linear η (n + 1) x = η x + Parking.walkOp (cslt_linear η n) x := rfl
        _ = η x + Parking.walkOp (fun z => ∑' y,
              Parking.CriticalScale.greenTime d n z y * η y) x := by
          rw [show cslt_linear η n = (fun z =>
              ∑' y, Parking.CriticalScale.greenTime d n z y * η y) by
                funext z; exact ih z]
        _ = η x + ∑' y, Parking.walkOp (fun z =>
              Parking.CriticalScale.greenTime d n z y * η y) x := by rw [hcomm]
        _ = η x + ∑' y, (Parking.CriticalScale.greenTime d (n + 1) x y * η y -
              Parking.CriticalScale.heatKernel d 0 x y * η y) := by
          congr 1
          exact tsum_congr hwalk
        _ = ∑' y, Parking.CriticalScale.greenTime d (n + 1) x y * η y := by
          rw [hnext.tsum_sub hzero, hzero_sum]
          ring

/-- The finite-sum form of `cslt_linear_green`, restricting the sum to
`LatticeProb.boxFinset x n`, outside which the truncated Green kernel vanishes. -/
theorem Parking.External.cslt_linear_green_finset {d : ℕ}
    (η : Parking.Site d → ℝ) (n : ℕ) (x : Parking.Site d) :
    cslt_linear η n x =
      ∑ y ∈ LatticeProb.boxFinset x n,
        Parking.CriticalScale.greenTime d n x y * η y := by
  rw [cslt_linear_green]
  exact tsum_eq_sum fun y hy => by
    rw [cslt_green_zero_of_not_mem hy, zero_mul]

-- FROZEN-STATEMENT-BEGIN
/-- The critical-scale lower-tail bound, proved rather than assumed. -/
theorem Parking.External.criticalScaleLowerTail : Parking.External.CriticalScaleLowerTail
-- FROZEN-STATEMENT-END
:= by
  intro hVar hBerry d hd hd3 ν₀ M hν₀ a ha ha'
  have hVar' : Sandpile.External.VarianceScale := hVar
  have hBerry' : Sandpile.External.MultivariateBerryEsseen := hBerry
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    Sandpile.exists_critical_toppling_bound hVar' hBerry' d hd hd3 ν₀ M hν₀ a ha ha'
  refine ⟨c, C, hc, hC, ?_⟩
  intro ν hprob hmean hvarpos hvar_top hint hν₀var hM t L ht hL hLa
  letI : IsProbabilityMeasure ν := hprob
  have hvar_ge : ν₀ ^ 2 ≤ variance (id : ℝ → ℝ) ν := by
    have htmp : (ENNReal.ofReal (ν₀ ^ 2)).toReal ≤
        (evariance (id : ℝ → ℝ) ν).toReal :=
      (ENNReal.toReal_le_toReal (by simp) hvar_top.ne).mpr hν₀var
    simpa [variance, ENNReal.toReal_ofReal (sq_nonneg ν₀)] using htmp
  have hvar_real : 0 < variance (id : ℝ → ℝ) ν :=
    ENNReal.toReal_pos (ne_of_gt hvarpos) (ne_of_lt hvar_top)
  have hodo0 : ∀ s : ℕ, ∀ σ : Parking.Site d → ℝ,
      Parking.CriticalScale.odometer σ s = Sandpile.odometer σ s := by
    intro s
    induction s with
    | zero => intro σ; rfl
    | succ s ih =>
      intro σ
      funext x
      simp [Parking.CriticalScale.odometer, Sandpile.odometer,
        Parking.CriticalScale.relax, Sandpile.relax, ih]
  have hodo : ∀ σ : Parking.Site d → ℝ,
      Parking.CriticalScale.odometer σ t = Sandpile.odometer σ t := hodo0 t
  have hreal := hbound ν hprob hmean hvar_real hint hvar_ge hM t L ht hL hLa
  have hL0 : 0 ≤ L := by linarith
  have hrem : 0 ≤ Parking.CriticalScale.lowerTailRemainder d t L a :=
    Parking.CriticalScale.lowerTailRemainder_nonneg d t hL0
  have hrhs : 0 ≤ C * L ^ (-c) + C * Parking.CriticalScale.lowerTailRemainder d t L a := by
    positivity
  have hevent : {σ : Parking.Site d → ℝ |
      Parking.CriticalScale.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} =
      {σ : Sandpile.Site d → ℝ |
        Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} := by
    ext σ
    simp only [Set.mem_setOf_eq]
    rw [congrFun (hodo σ) 0]
  letI : IsProbabilityMeasure (Parking.CriticalScale.centeredMassLaw d ν) :=
    Parking.CriticalScale.centeredMassLaw_isProbability d ν
  have hPtop : Parking.CriticalScale.centeredMassLaw d ν
      {σ | Parking.CriticalScale.odometer σ t 0 ≤
        (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / L} ≠ ⊤ :=
    measure_ne_top (Parking.CriticalScale.centeredMassLaw d ν) _
  apply (ENNReal.toReal_le_toReal hPtop ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hrhs]
  rw [← hevent] at hreal
  simpa [Parking.CriticalScale.centeredMassLaw, Sandpile.centeredMassLaw,
    Sandpile.massLaw, Parking.CriticalScale.lowerTailRemainder] using hreal
