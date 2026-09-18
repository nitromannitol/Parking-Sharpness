/-
The origin has an infinite odometer with probability bounded below.

Step 2 of `prop:everyone-settles` (`parking.tex:1510-1526`): the Paley-Zygmund
bound of `Parking.exists_odometer_lower_prob` holds at every `n`, and
`E u_n(0) + log n` tends to infinity, so for every level `M` there is an `n` at
which the event of that lemma forces `U_n(0) ≥ M`.  The events
`{U_∞(0) ≥ M}` decrease to `{U_∞(0) = ∞}`, which therefore has probability at
least the Paley-Zygmund constant.
-/
import Parking.Support.OdometerLower

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology
open scoped ENNReal

variable {d : ℕ}

theorem Ulimit_eq_top_iff (ω : Data d) (x : Site d) :
    Parking.Ulimit ω x = ⊤ ↔ ∀ M : ℕ, ∃ n : ℕ, M ≤ Parking.U ω n x := by
  unfold Parking.Ulimit
  rw [iSup_eq_top]
  constructor
  · intro h M
    obtain ⟨n, hn⟩ := h (M : ℕ∞) (by exact_mod_cast ENat.coe_lt_top M)
    exact ⟨n, le_of_lt (by exact_mod_cast hn)⟩
  · intro h b hb
    lift b to ℕ using hb.ne
    obtain ⟨n, hn⟩ := h (b + 1)
    exact ⟨n, by exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hn⟩

theorem exists_two_le_log_ge (b : ℝ) : ∃ n : ℕ, 2 ≤ n ∧ b ≤ Real.log n := by
  refine ⟨max 2 ⌈Real.exp b⌉₊, le_max_left _ _, ?_⟩
  have hn2 : 2 ≤ max 2 ⌈Real.exp b⌉₊ := le_max_left _ _
  have hpos : (0:ℝ) < ((max 2 ⌈Real.exp b⌉₊ : ℕ) : ℝ) := by
    have : (0:ℕ) < max 2 ⌈Real.exp b⌉₊ := lt_of_lt_of_le (by norm_num) hn2
    exact_mod_cast this
  rw [Real.le_log_iff_exp_le hpos]
  refine le_trans (Nat.le_ceil (Real.exp b)) ?_
  exact_mod_cast Nat.cast_le.mpr (le_max_right 2 ⌈Real.exp b⌉₊)

theorem exists_prob_Ulimit_top (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : CriticalLaw ν) :
    ∃ a : ℝ, 0 < a ∧ a ≤ (law d ν).real {ω : Data d | Parking.Ulimit ω 0 = ⊤} := by
  haveI := hν.prob
  haveI := law_isProb hd ν
  obtain ⟨c, a, hc, ha, hlow⟩ :=
    exists_odometer_lower_prob hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
  classical
  set B : ℕ → Set (Data d) := fun M => ⋃ n : ℕ, {ω : Data d | M ≤ Parking.U ω n 0} with hB
  have hBmeas : ∀ M, MeasurableSet (B M) := by
    intro M
    exact MeasurableSet.iUnion fun n =>
      measurableSet_le measurable_const (measurable_U n 0)
  have hBanti : Antitone B := by
    intro M M' hMM'
    refine Set.iUnion_mono fun n => ?_
    intro ω hω
    exact le_trans hMM' hω
  have haB : ∀ M : ℕ, a ≤ (law d ν).real (B M) := by
    intro M
    obtain ⟨n, hn2, hlogn⟩ := exists_two_le_log_ge ((M : ℝ) / c)
    have hMle : (M : ℝ) ≤ c * (meanu (law d ν) n + Real.log n) := by
      have hmu : (0:ℝ) ≤ meanu (law d ν) n := integral_nonneg fun ω => uOf_nonneg ω n 0
      have h1 : (M : ℝ) ≤ c * Real.log n := by
        rw [div_le_iff₀ hc] at hlogn
        linarith
      nlinarith
    refine le_trans (hlow n hn2) ?_
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    have hlt : c * (meanu (law d ν) n + Real.log n) < ((Parking.U ω n 0 : ℕ) : ℝ) := hω
    have : (M : ℝ) < ((Parking.U ω n 0 : ℕ) : ℝ) := lt_of_le_of_lt hMle hlt
    exact Set.mem_iUnion.mpr ⟨n, le_of_lt (by exact_mod_cast this)⟩
  have hset : {ω : Data d | Parking.Ulimit ω 0 = ⊤} = ⋂ M : ℕ, B M := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, hB, Set.mem_iUnion]
    exact Ulimit_eq_top_iff ω 0
  refine ⟨a, ha, ?_⟩
  rw [hset]
  have hlim : Tendsto (fun M => (law d ν) (B M)) atTop (𝓝 ((law d ν) (⋂ M, B M))) :=
    tendsto_measure_iInter_atTop (fun M => (hBmeas M).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top _ _⟩
  have hge : ENNReal.ofReal a ≤ (law d ν) (⋂ M, B M) := by
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun M => ?_)
    have h1 := haB M
    rw [measureReal_def] at h1
    calc ENNReal.ofReal a ≤ ENNReal.ofReal (((law d ν) (B M)).toReal) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (law d ν) (B M) := ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [measureReal_def]
  calc a = (ENNReal.ofReal a).toReal := (ENNReal.toReal_ofReal ha.le).symm
    _ ≤ ((law d ν) (⋂ M, B M)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) hge

end Parking
