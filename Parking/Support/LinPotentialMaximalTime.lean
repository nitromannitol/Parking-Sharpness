/-
**The discrete maximal inequality of `Parking.Support.LinPotentialMaximal`, extended over a
range of TIMES too, and re-centered at an arbitrary site.**

The randomized cutoff-to-true bound
(`Parking.abs_stoppingSup_sub_cutoffStoppingSup_pathwise`,
`Parking/Support/StoppingCutoffPathwise.lean`) needs a bound `M` on the reward
`Parking.cutoffReward F' A₂`, i.e. on `sup_{k ≤ n₀, y ∈ box A₂} |Parking.linPotential η
(n₀-k) y|` -- a sup over a RANGE of times `m := n₀-k ∈ [0,n₀]`, not the single fixed time
`Parking.Support.LinPotentialMaximal`'s own maximal inequality bounds.  This module supplies
that extension by ONE further union bound over the (fixed, finite) time range
`Finset.Icc 1 N` (`Parking.exists_linPotential_maximal_tail_time`), at the SAME rate (the
bound at any `m ≤ N` is dominated by the SAME formula evaluated at the common scale `N`,
`Parking.exists_linPotential_point_tail_mono`, since the underlying kernel-norm bounds
`Parking.l2Norm_green_le`/`supAbs_green_le` are monotone in the time argument); and then
RE-CENTERS the resulting maximal inequality at an arbitrary site `z0` (needed since the
reward `F'` above is itself already shifted to start at `z0`) via the shared library's
translation invariance of the i.i.d. scenery law (`LatticeProb.iidLaw_map_shiftConf`) and the
translation covariance of `Parking.linPotential` itself
(`Parking.linPotential_comp_add`, a short reindexing of `Parking.linPotential_eq_sum`).

No `External` is registered or consumed: every theorem here is proved, not cited.
-/
import Parking.Support.LinPotentialMaximal
import Parking.Support.Invariance
import Parking.Support.BoxTranslation

noncomputable section

namespace Parking

open MeasureTheory LatticeProb Finset Parking.Generic.MinProduct

variable {d : ℕ}

/-! ### The per-point tail bound, evaluated at a common uniform scale -/

/-- **The per-point tail bound at a COMMON uniform scale `N ≥ m`**: `Parking.
exists_linPotential_point_tail`'s bound at `m`'s own scale only gets weaker (larger) as the
scale used grows, so the SAME formula evaluated at `N` bounds every `m ≤ N` simultaneously. -/
theorem exists_linPotential_point_tail_mono (hd1 : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (m : ℕ), 1 ≤ m → m ≤ N →
      ∀ (y : Site d) (r : ℝ), 0 < r →
      ((iidLaw d (realLaw ν)) {η | r ≤ |linPotential η m y|}).toReal
        ≤ C * Real.exp (-(c * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ)))) := by
  obtain ⟨c0, C0, hc0, hC0, hpt⟩ := exists_linPotential_point_tail hd1 ν hν
  set Cg1 : ℝ := 1 + Real.sqrt (LatticeProb.diagConst d / Real.sqrt 2 ^ d) with hCg1def
  set Cg2 : ℝ := 1 + LatticeProb.diagConst d with hCg2def
  have hCg1pos : 0 < Cg1 := by rw [hCg1def]; positivity
  have hCg2pos : 0 < Cg2 := by rw [hCg2def]; have := LatticeProb.diagConst_pos d; linarith
  set κ : ℝ := min (1 / Cg1 ^ 2) (1 / Cg2) with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact lt_min (div_pos one_pos (pow_pos hCg1pos 2)) (div_pos one_pos hCg2pos)
  refine ⟨c0 * κ, C0, mul_pos hc0 hκpos, hC0, ?_⟩
  intro N hN m hm hmN y r hr
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hb := hpt m hm y r hr
  have hL2bm : l2Norm (fun z => green d m (y - z)) ≤ Cg1 * N := by
    refine (l2Norm_green_le hd1 m hm y).trans ?_
    have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    exact mul_le_mul_of_nonneg_left hmR hCg1pos.le
  have hSupbm : supAbs (fun z => green d m (y - z)) ≤ Cg2 * N := by
    refine (supAbs_green_le hd1 m hm y).trans ?_
    have hmR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN
    exact mul_le_mul_of_nonneg_left hmR hCg2pos.le
  have hL2posm : 0 < l2Norm (fun z => green d m (y - z)) := l2Norm_green_pos m hm y
  have hSupposm : 0 < supAbs (fun z => green d m (y - z)) := supAbs_green_pos m hm y
  have hminkey : κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ))
      ≤ min (r ^ 2 / (Cg1 * N) ^ 2) (r / (Cg2 * N)) := by
    have heq1 : r ^ 2 / (Cg1 * N) ^ 2 = (1 / Cg1 ^ 2) * (r ^ 2 / (N : ℝ) ^ 2) := by
      rw [mul_pow]; field_simp
    have heq2 : r / (Cg2 * N) = (1 / Cg2) * (r / (N : ℝ)) := by field_simp
    rw [heq1, heq2, hκdef]
    exact min_mul_min_le (1 / Cg1 ^ 2) (1 / Cg2) (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ))
      (by positivity) (by positivity) (by positivity) (by positivity)
  have hL2ratio : r ^ 2 / (Cg1 * N) ^ 2 ≤ r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg r) (pow_pos hL2posm 2)
      (pow_le_pow_left₀ hL2posm.le hL2bm 2)
  have hSupratio : r / (Cg2 * N) ≤ r / supAbs (fun z => green d m (y - z)) :=
    div_le_div_of_nonneg_left hr.le hSupposm hSupbm
  have hminratio : min (r ^ 2 / (Cg1 * N) ^ 2) (r / (Cg2 * N))
      ≤ min (r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2)
          (r / supAbs (fun z => green d m (y - z))) :=
    min_le_min hL2ratio hSupratio
  have hchain : κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ))
      ≤ min (r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2)
          (r / supAbs (fun z => green d m (y - z))) :=
    hminkey.trans hminratio
  have hmulle : c0 * (κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ)))
      ≤ c0 * min (r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2)
          (r / supAbs (fun z => green d m (y - z))) :=
    mul_le_mul_of_nonneg_left hchain hc0.le
  have hexple : Real.exp (-(c0 * min (r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2)
          (r / supAbs (fun z => green d m (y - z)))))
      ≤ Real.exp (-(c0 * κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ)))) := by
    rw [Real.exp_le_exp]
    have hre : c0 * κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ))
        = c0 * (κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ))) := by ring
    rw [hre]; exact neg_le_neg hmulle
  have hCmulle : C0 * Real.exp (-(c0 * min (r ^ 2 / (l2Norm (fun z => green d m (y - z))) ^ 2)
          (r / supAbs (fun z => green d m (y - z)))))
      ≤ C0 * Real.exp (-(c0 * κ * min (r ^ 2 / (N : ℝ) ^ 2) (r / (N : ℝ)))) :=
    mul_le_mul_of_nonneg_left hexple hC0.le
  exact hb.trans hCmulle

/-! ### The joint time-space maximal inequality, at the origin -/

/-- **The joint time-space maximal inequality**: the probability that `linPotential η · ·`
exceeds `M` somewhere in the time range `[1, N]` and the box `boxFinset 0 A` is controlled by
the SAME rate as the single-time maximal inequality (`Parking.
exists_linPotential_maximal_tail`), at the extra cost of a factor `N` (cardinality of the time
range) in the prefactor. -/
theorem exists_linPotential_maximal_tail_time (hd1 : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (A : ℕ) (M : ℝ), 0 < M →
      ((iidLaw d (realLaw ν))
          {η | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η m y|}).toReal
        ≤ C * N * (2 * A + 1) ^ d * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI hμP : IsProbabilityMeasure (iidLaw d (realLaw ν)) :=
    inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : Site d => realLaw ν))
  obtain ⟨c, C, hc, hC, hmono⟩ := exists_linPotential_point_tail_mono hd1 ν hν
  refine ⟨c, C, hc, hC, ?_⟩
  intro N hN A M hM
  set S : Set (Site d → ℝ) :=
      {η | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η m y|}
    with hSdef
  have hEsub : S ⊆ ⋃ m ∈ Finset.Icc 1 N, ⋃ y ∈ boxFinset (0 : Site d) A,
      {η : Site d → ℝ | M ≤ |linPotential η m y|} := by
    intro η hη
    obtain ⟨m, hm, y, hy, hyM⟩ := hη
    exact Set.mem_biUnion hm (Set.mem_biUnion hy hyM)
  have hstep1 : (iidLaw d (realLaw ν)).real S
      ≤ (iidLaw d (realLaw ν)).real (⋃ m ∈ Finset.Icc 1 N, ⋃ y ∈ boxFinset (0 : Site d) A,
          {η : Site d → ℝ | M ≤ |linPotential η m y|}) :=
    measureReal_mono hEsub (measure_ne_top _ _)
  have hstep3 : ∀ m ∈ Finset.Icc 1 N, (iidLaw d (realLaw ν)).real
        (⋃ y ∈ boxFinset (0 : Site d) A, {η : Site d → ℝ | M ≤ |linPotential η m y|})
      ≤ ∑ y ∈ boxFinset (0 : Site d) A, (iidLaw d (realLaw ν)).real
          {η : Site d → ℝ | M ≤ |linPotential η m y|} :=
    fun m _ => measureReal_biUnion_finset_le _ _
  have hpoint : ∀ m ∈ Finset.Icc 1 N, ∀ y ∈ boxFinset (0 : Site d) A,
      (iidLaw d (realLaw ν)).real {η : Site d → ℝ | M ≤ |linPotential η m y|}
        ≤ C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))) := by
    intro m hm y _
    rw [Finset.mem_Icc] at hm
    exact hmono N hN m hm.1 hm.2 y M hM
  have hcard : (boxFinset (0 : Site d) A).card = (2 * A + 1) ^ d := card_boxFinset 0 A
  have hstep5 : ∀ m ∈ Finset.Icc 1 N, ∑ _y ∈ boxFinset (0 : Site d) A,
        C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ))))
      = (2 * A + 1) ^ d * (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ))))) := by
    intro m _
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    ring
  have hIccCard : (Finset.Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
  have hfinal : (iidLaw d (realLaw ν)).real S
      ≤ (N : ℕ) • ((2 * A + 1) ^ d * (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))))) := by
    refine hstep1.trans ?_
    calc (iidLaw d (realLaw ν)).real (⋃ m ∈ Finset.Icc 1 N, ⋃ y ∈ boxFinset (0 : Site d) A,
          {η : Site d → ℝ | M ≤ |linPotential η m y|})
        ≤ ∑ m ∈ Finset.Icc 1 N, (iidLaw d (realLaw ν)).real
            (⋃ y ∈ boxFinset (0 : Site d) A, {η : Site d → ℝ | M ≤ |linPotential η m y|}) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 N, ∑ y ∈ boxFinset (0 : Site d) A,
            (iidLaw d (realLaw ν)).real {η : Site d → ℝ | M ≤ |linPotential η m y|} :=
          Finset.sum_le_sum hstep3
      _ ≤ ∑ m ∈ Finset.Icc 1 N, (2 * A + 1) ^ d *
            (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ))))) := by
          refine Finset.sum_le_sum fun m hm => ?_
          rw [← hstep5 m hm]; exact Finset.sum_le_sum (hpoint m hm)
      _ = (Finset.Icc 1 N).card •
            ((2 * A + 1) ^ d * (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))))) := by
          rw [Finset.sum_const]
      _ = (N : ℕ) •
            ((2 * A + 1) ^ d * (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))))) := by
          rw [hIccCard]
  rw [nsmul_eq_mul] at hfinal
  rw [← measureReal_def]
  calc (iidLaw d (realLaw ν)).real S
      ≤ (N : ℝ) * ((2 * A + 1) ^ d * (C * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))))) :=
        hfinal
    _ = C * N * (2 * A + 1) ^ d * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))) := by
        ring

/-! ### Re-centering the maximal inequality at an arbitrary site -/

/-- **The translation covariance of `Parking.linPotential`**: shifting the scenery by `z0`
shifts the evaluation point by `z0`.  A reindexing of `Parking.linPotential_eq_sum` along the
box translation `Parking.mem_boxFinset_translate`. -/
theorem linPotential_comp_add (η : Site d → ℝ) (z0 : Site d) (m : ℕ) (y : Site d) :
    linPotential (fun z => η (z + z0)) m y = linPotential η m (y + z0) := by
  rw [linPotential_eq_sum, linPotential_eq_sum]
  refine Finset.sum_bij' (fun z _ => z + z0) (fun z' _ => z' - z0) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    exact (mem_boxFinset_translate z0 y z m).mpr hz
  · intro z' hz'
    have h1 : (z' - z0) + z0 ∈ boxFinset (y + z0) m := by simpa using hz'
    exact (mem_boxFinset_translate z0 y (z' - z0) m).mp (by simpa using h1)
  · intro z hz; simp
  · intro z' hz'; simp
  · intro z hz
    have heq : y - z = y + z0 - (z + z0) := by abel
    rw [heq]

theorem measurable_linPotential_pt (m : ℕ) (y : Site d) :
    Measurable (fun η : Site d → ℝ => linPotential η m y) := by
  have heq : (fun η : Site d → ℝ => linPotential η m y)
      = fun η => ∑ z ∈ boxFinset y m, η z * green d m (y - z) := by
    funext η; exact linPotential_eq_sum η m y
  rw [heq]
  exact Finset.measurable_sum _ (fun z _ => (measurable_pi_apply z).mul measurable_const)

theorem measurableSet_maximal_tail_time_event (N A : ℕ) (M : ℝ) :
    MeasurableSet {η : Site d → ℝ |
      ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η m y|} := by
  have heq : {η : Site d → ℝ |
      ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η m y|}
      = ⋃ m ∈ Finset.Icc 1 N, ⋃ y ∈ boxFinset (0 : Site d) A,
          {η : Site d → ℝ | M ≤ |linPotential η m y|} := by
    ext η; simp [Set.mem_iUnion]
  rw [heq]
  refine Finset.measurableSet_biUnion _ (fun m _ => Finset.measurableSet_biUnion _ (fun y _ => ?_))
  exact measurableSet_le measurable_const (measurable_linPotential_pt m y).abs

/-- **The maximal inequality, shifted to a box centered at an arbitrary site `z0`.**
`LatticeProb.iidLaw_map_shiftConf`'s translation invariance of the i.i.d. scenery law, combined
with `Parking.linPotential_comp_add`'s translation covariance, transports the origin-centered
maximal inequality (`Parking.exists_linPotential_maximal_tail_time`) to a box centered
anywhere, at exactly the SAME rate. -/
theorem exists_linPotential_maximal_tail_time_shift (hd1 : 1 ≤ d) (ν : Measure ℤ)
    (hν : CriticalLaw ν) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (z0 : Site d) (N : ℕ), 1 ≤ N → ∀ (A : ℕ) (M : ℝ), 0 < M →
      ((iidLaw d (realLaw ν))
          {η | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A,
              M ≤ |linPotential η m (y + z0)|}).toReal
        ≤ C * N * (2 * A + 1) ^ d * Real.exp (-(c * min (M ^ 2 / (N : ℝ) ^ 2) (M / (N : ℝ)))) := by
  haveI := hν.prob
  haveI hν0P : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  obtain ⟨c, C, hc, hC, hmain⟩ := exists_linPotential_maximal_tail_time hd1 ν hν
  refine ⟨c, C, hc, hC, ?_⟩
  intro z0 N hN A M hM
  set T : Set (Site d → ℝ) :=
      {η | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A, M ≤ |linPotential η m y|}
    with hTdef
  have hTmeas : MeasurableSet T := measurableSet_maximal_tail_time_event N A M
  have hfmeas : Measurable (fun η : Site d → ℝ => fun x => η (x + z0)) :=
    measurable_pi_lambda _ fun x => measurable_pi_apply (x + z0)
  have hshift : (iidLaw d (realLaw ν)).map (fun η : Site d → ℝ => fun x => η (x + z0))
      = iidLaw d (realLaw ν) := LatticeProb.iidLaw_map_shiftConf (realLaw ν) z0
  have hpre : (fun η : Site d → ℝ => fun x => η (x + z0)) ⁻¹' T
      = {η : Site d → ℝ | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A,
          M ≤ |linPotential η m (y + z0)|} := by
    ext η
    simp only [Set.mem_preimage, hTdef, Set.mem_setOf_eq]
    constructor
    · rintro ⟨m, hm, y, hy, hle⟩
      refine ⟨m, hm, y, hy, ?_⟩
      rwa [← linPotential_comp_add η z0 m y]
    · rintro ⟨m, hm, y, hy, hle⟩
      refine ⟨m, hm, y, hy, ?_⟩
      rwa [linPotential_comp_add η z0 m y]
  have hmapeq : (iidLaw d (realLaw ν))
      {η : Site d → ℝ | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A,
          M ≤ |linPotential η m (y + z0)|}
      = (iidLaw d (realLaw ν)) T := by
    rw [← hpre, ← Measure.map_apply hfmeas hTmeas, hshift]
  rw [show ((iidLaw d (realLaw ν))
        {η : Site d → ℝ | ∃ m ∈ Finset.Icc 1 N, ∃ y ∈ boxFinset (0 : Site d) A,
            M ≤ |linPotential η m (y + z0)|}).toReal
      = ((iidLaw d (realLaw ν)) T).toReal from by rw [hmapeq]]
  exact hmain N hN A M hM

end Parking

end
