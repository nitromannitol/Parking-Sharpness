/-
Step 1 of `prop:everyone-settles` (`parking.tex:1496-1508`): every particle
settles and every hole is filled.

The survivor density `S_t` tends to zero, because `cor:growth` bounds it by
`C (t+1)^{-d/4}` in dimensions at most three and by `C log(t+2)/(t+1)` in
dimensions at least four.  A nonnegative integer variable whose mean tends to
zero vanishes at some time almost surely: the events `{f_t ≠ 0}` have measure at
most the mean of `f_t` by Markov's inequality, so their intersection is null.
Applied to the number of particles started at the origin and still active, that
is the statement that the origin's particles all settle; applied to the unfilled
holes at the origin, whose mean is again `S_t` by `lem:transport` and
`lem:activity-holes`, it is the statement that the origin's holes are all
filled.  Translation invariance of the law and countability of the lattice carry
both statements to every site.
-/
import Parking.Frozen.Growth
import Parking.Support.CouplingTarget
import Parking.Support.DensitySequence

noncomputable section
namespace Parking
open MeasureTheory LatticeProb Filter Topology

variable {d : ℕ}

/-! ### Two limits -/

/-- A negative power of `t + 1` tends to zero along the integers. -/
theorem rpow_neg_shift_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℕ => ((t : ℝ) + 1) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- `log(t+2)/(t+1)` tends to zero along the integers. -/
theorem log_div_tendsto :
    Tendsto (fun t : ℕ => Real.log ((t : ℝ) + 2) / ((t : ℝ) + 1)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h2 : Tendsto (fun t : ℕ => Real.log ((t : ℝ) + 2) / ((t : ℝ) + 2)) atTop (𝓝 0) :=
    hlog.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have h3 : Tendsto (fun t : ℕ => 2 * (Real.log ((t : ℝ) + 2) / ((t : ℝ) + 2))) atTop (𝓝 0) := by
    simpa using h2.const_mul (2 : ℝ)
  refine squeeze_zero (fun t => ?_) (fun t => ?_) h3
  · have hn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h1 : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by linarith)
    exact div_nonneg h1 (by linarith)
  · have hn : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    have h1 : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) := Real.log_nonneg (by linarith)
    rw [div_le_iff₀ (by linarith : (0:ℝ) < (t : ℝ) + 1)]
    have h5 : (1:ℝ) ≤ 2 * ((t:ℝ)+1) / ((t:ℝ)+2) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < (t:ℝ)+2)]; linarith
    calc Real.log ((t:ℝ)+2) = Real.log ((t:ℝ)+2) * 1 := by ring
      _ ≤ Real.log ((t:ℝ)+2) * (2 * ((t:ℝ)+1) / ((t:ℝ)+2)) := by nlinarith
      _ = 2 * (Real.log ((t:ℝ)+2) / ((t:ℝ)+2)) * ((t:ℝ)+1) := by field_simp

/-! ### A nonnegative integer variable whose mean vanishes -/

/-- If the means of a sequence of nonnegative integer variables tend to zero,
then almost surely some term of the sequence vanishes.  Markov's inequality
bounds the measure of `{f_t ≠ 0}` by the mean of `f_t`, and the intersection of
those events is contained in each of them. -/
theorem ae_exists_eq_zero_of_tendsto {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : ℕ → Ω → ℕ) (hmeas : ∀ t, Measurable (f t))
    (hint : ∀ t, Integrable (fun ω => (f t ω : ℝ)) P)
    (hlim : Tendsto (fun t => ∫ ω, (f t ω : ℝ) ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, ∃ t : ℕ, f t ω = 0 := by
  classical
  set E : ℕ → Set Ω := fun t => {ω | (1 : ℝ) ≤ (f t ω : ℝ)} with hE
  have hEm : ∀ t, MeasurableSet (E t) := fun t =>
    measurableSet_le measurable_const
      ((measurable_from_countable' fun n : ℕ => (n : ℝ)).comp (hmeas t))
  have hMark : ∀ t, (P (E t)).toReal ≤ ∫ ω, (f t ω : ℝ) ∂P := by
    intro t
    have hnn : (0 : Ω → ℝ) ≤ᵐ[P] fun ω => (f t ω : ℝ) :=
      Filter.Eventually.of_forall fun ω => by positivity
    have hM := mul_meas_ge_le_integral_of_nonneg hnn (hint t) 1
    simpa [hE, measureReal_def] using hM
  have hsub : ∀ t, (P (⋂ s, E s)).toReal ≤ ∫ ω, (f t ω : ℝ) ∂P := by
    intro t
    refine le_trans (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono ?_)) (hMark t)
    exact Set.iInter_subset _ t
  have h0 : (P (⋂ s, E s)).toReal ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hsub)
  have hz : P (⋂ s, E s) = 0 := by
    have h1 := le_antisymm h0 ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).mp h1 with h | h
    · exact h
    · exact absurd h (measure_ne_top P _)
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ s, E s := by
    rw [ae_iff]
    have hset : {a | ¬ a ∉ ⋂ s, E s} = ⋂ s, E s := by ext a; simp
    rw [hset]; exact hz
  filter_upwards [hae] with ω hω
  rw [Set.mem_iInter] at hω
  obtain ⟨t, ht⟩ := not_forall.mp hω
  refine ⟨t, ?_⟩
  by_contra hne
  exact ht (by
    have h1 : (1 : ℕ) ≤ f t ω := Nat.one_le_iff_ne_zero.mpr hne
    simpa [hE] using (Nat.one_le_cast (α := ℝ)).mpr h1)

/-! ### Transport of an almost sure statement by a translation -/

/-- The law of the data is translation invariant, so an almost sure property is
almost surely true of every translate of the realization. -/
theorem ae_shiftData (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν] (v : Site d)
    {p : Data d → Prop} (hp : MeasurableSet {ω : Data d | p ω})
    (h : ∀ᵐ ω ∂(law d ν), p ω) : ∀ᵐ ω ∂(law d ν), p (shiftData v ω) := by
  have hmap := Parking.law_map_shiftData (d := d) hd ν v
  rw [← hmap] at h
  exact (MeasureTheory.ae_map_iff (Parking.measurable_shiftData v).aemeasurable hp).mp h

/-! ### The survivor density tends to zero -/

/-- `S_t → 0`.  In dimensions at most three `cor:growth` bounds `S_t` by
`C (t+1)^{-d/4}`, and in dimensions at least four by `C log(t+2)/(t+1)`. -/
theorem S_tendsto_zero (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    Tendsto (Parking.S (Parking.law d ν)) atTop (𝓝 0) := by
  have hg := Parking.Frozen.growth hGrowth hBernstein hConcentration hGreenNorms d hd ν hν
  rcases le_or_gt d 3 with h3 | h4
  · obtain ⟨c, C, hc, hcC, -, hS⟩ := hg.1 h3
    refine squeeze_zero (fun t => S_nonneg _ t) (fun t => (hS t).2) ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hd4 : 0 < (d : ℝ) / 4 := by linarith
    simpa using (rpow_neg_shift_tendsto ((d : ℝ) / 4) hd4).const_mul C
  · obtain ⟨c, C, hc, hcC, -, hS⟩ := hg.2 (by omega)
    refine squeeze_zero (fun t => S_nonneg _ t) (fun t => (hS t).2) ?_
    have := log_div_tendsto.const_mul C
    simpa [mul_div_assoc] using this

/-! ### Every particle settles -/

/-- A site with no surviving particle after round `t₀` has no active particle
after any later round. -/
theorem inactive_of_survivorsFrom_eq_zero {D : Driver d} {t₀ : ℕ} {x : Site d}
    (h : LatticeProb.survivorsFrom D t₀ x = 0) (i t : ℕ) (ht : t₀ ≤ t) :
    (LatticeProb.state D t).active (x, i) = false := by
  classical
  rcases Bool.eq_false_or_eq_true ((LatticeProb.state D t).active (x, i)) with hc | hc
  · exfalso
    have h0 : (LatticeProb.state D t₀).active (x, i) = true := LatticeProb.active_of_le ht hc
    have hi : i < (D.eta x).toNat := LatticeProb.lt_toNat_of_active h0
    have hmem : i ∈ (Finset.range (D.eta x).toNat).filter
        (fun i => (LatticeProb.state D t₀).active (x, i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h0⟩
    have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
    rw [← LatticeProb.survivorsFrom, h] at hpos
    exact absurd hpos (lt_irrefl 0)
  · exact hc

/-! ### The origin -/

/-- Almost surely the origin's particles have all settled at some round. -/
theorem ae_exists_survivors_zero (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ᵐ ω ∂(Parking.law d ν), ∃ t : ℕ,
      LatticeProb.survivorsFrom (Parking.toDriver ω) t 0 = 0 := by
  haveI := hν.prob
  haveI := Parking.law_isProb (d := d) hd ν
  have hint := hν.integrable_abs
  have htr := Parking.Frozen.transport d hd ν inferInstance hint
  refine Parking.ae_exists_eq_zero_of_tendsto (Parking.law d ν)
      (fun t ω => LatticeProb.survivorsFrom (Parking.toDriver ω) t 0)
      (fun t => Parking.measurable_survivorsFrom t 0)
      (fun t => (htr.1 t).2.1) ?_
  exact Parking.S_tendsto_zero hGrowth hBernstein hConcentration hGreenNorms d hd ν hν

/-- Almost surely the holes at the origin are all filled at some round.  Their
mean is again `S_t`, by `lem:transport` and `lem:activity-holes`. -/
theorem ae_exists_holes_zero (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ᵐ ω ∂(Parking.law d ν), ∃ t : ℕ, Parking.H ω t 0 = 0 := by
  haveI := hν.prob
  haveI := Parking.law_isProb (d := d) hd ν
  have hint := hν.integrable_abs
  have hHint : ∀ t : ℕ,
      Integrable (fun ω : Data d => (Parking.H ω t 0 : ℝ)) (Parking.law d ν) := by
    intro t
    haveI : IsProbabilityMeasure (LatticeProb.iidLaw d ν) := by
      unfold LatticeProb.iidLaw; infer_instance
    have hmap : (LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0) = ν :=
      Measure.infinitePi_map_eval _ 0
    have hi0 : Integrable (fun η : Site d → ℤ => |(η 0 : ℝ)|) (LatticeProb.iidLaw d ν) := by
      have hi : Integrable (fun k : ℤ => |(k : ℝ)|)
          ((LatticeProb.iidLaw d ν).map (fun η : Site d → ℤ => η 0)) := by rw [hmap]; exact hint
      exact (integrable_map_measure (g := fun k : ℤ => |(k : ℝ)|)
        (f := fun η : Site d → ℤ => η 0) (μ := LatticeProb.iidLaw d ν)
        (by rw [hmap]; exact hint.aestronglyMeasurable)
        (measurable_pi_apply (0 : Site d)).aemeasurable).mp hi
    exact Parking.integrable_H_data hd (fun v => Parking.iidLaw_map_shiftConf' ν v) hi0 t 0
  refine Parking.ae_exists_eq_zero_of_tendsto (Parking.law d ν)
      (fun t ω => Parking.H ω t 0)
      (fun t => Parking.measurable_H t 0) hHint ?_
  have hmean : ∀ t : ℕ, ∫ ω, (Parking.H ω t 0 : ℝ) ∂(Parking.law d ν)
      = Parking.S (Parking.law d ν) t :=
    fun t => (Parking.mean_A_and_H_eq_S hd ν hint hν.mean t).2
  simp only [hmean]
  exact Parking.S_tendsto_zero hGrowth hBernstein hConcentration hGreenNorms d hd ν hν

/-! ### Every site -/

theorem measurableSet_exists_survivors_zero (d : ℕ) (y : Site d) :
    MeasurableSet {ω : Data d | ∃ t : ℕ, LatticeProb.survivorsFrom (toDriver ω) t y = 0} := by
  have hset : {ω : Data d | ∃ t : ℕ, LatticeProb.survivorsFrom (toDriver ω) t y = 0}
      = ⋃ t : ℕ, (fun ω : Data d => LatticeProb.survivorsFrom (toDriver ω) t y) ⁻¹' {0} := by
    ext ω; simp
  rw [hset]
  exact MeasurableSet.iUnion fun t =>
    (Parking.measurable_survivorsFrom t y) (measurableSet_singleton 0)

theorem measurableSet_exists_holes_zero (d : ℕ) (y : Site d) :
    MeasurableSet {ω : Data d | ∃ t : ℕ, Parking.H ω t y = 0} := by
  have hset : {ω : Data d | ∃ t : ℕ, Parking.H ω t y = 0}
      = ⋃ t : ℕ, (fun ω : Data d => Parking.H ω t y) ⁻¹' {0} := by
    ext ω; simp
  rw [hset]
  exact MeasurableSet.iUnion fun t => (Parking.measurable_H t y) (measurableSet_singleton 0)

/-- Translation invariance and countability carry the statement at the origin to
every site. -/
theorem ae_forall_survivors_zero (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (h0 : ∀ᵐ ω ∂(law d ν), ∃ t : ℕ, LatticeProb.survivorsFrom (toDriver ω) t 0 = 0) :
    ∀ᵐ ω ∂(law d ν), ∀ y : Site d, ∃ t : ℕ,
      LatticeProb.survivorsFrom (toDriver ω) t y = 0 := by
  rw [ae_all_iff]
  intro y
  have hs := ae_shiftData (d := d) hd ν y (measurableSet_exists_survivors_zero d 0) h0
  filter_upwards [hs] with ω hω
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [survivorsFrom_shiftData (v := y) (ω := ω) t 0, zero_add] at ht
  exact ht

/-- The same for the holes. -/
theorem ae_forall_holes_zero (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (h0 : ∀ᵐ ω ∂(law d ν), ∃ t : ℕ, Parking.H ω t 0 = 0) :
    ∀ᵐ ω ∂(law d ν), ∀ y : Site d, ∃ t : ℕ, Parking.H ω t y = 0 := by
  rw [ae_all_iff]
  intro y
  have hs := ae_shiftData (d := d) hd ν y (measurableSet_exists_holes_zero d 0) h0
  filter_upwards [hs] with ω hω
  obtain ⟨t, ht⟩ := hω
  refine ⟨t, ?_⟩
  rw [H_shiftData (v := y) (ω := ω) t 0, zero_add] at ht
  exact ht

/-! ### Step 1 of `prop:everyone-settles` -/

/-- **Every particle settles and every hole is filled.**  This is Step 1 of the
proof of `prop:everyone-settles` at `parking.tex:1496-1508`. -/
theorem ae_settle_and_fill (hGrowth : Parking.External.SandpileGrowth)
    (hBernstein : Parking.External.Bernstein)
    (hConcentration : Parking.External.UConcentration)
    (hGreenNorms : Parking.External.GreenNorms)
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℤ) (hν : Parking.CriticalLaw ν) :
    ∀ᵐ ω ∂(Parking.law d ν),
      (∀ p : Label d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
          (LatticeProb.state (Parking.toDriver ω) t).active p = false) ∧
      (∀ x : Site d, ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Parking.H ω t x = 0) := by
  haveI := hν.prob
  have hsurv := ae_forall_survivors_zero (d := d) hd ν
    (ae_exists_survivors_zero hGrowth hBernstein hConcentration hGreenNorms d hd ν hν)
  have hholes := ae_forall_holes_zero (d := d) hd ν
    (ae_exists_holes_zero hGrowth hBernstein hConcentration hGreenNorms d hd ν hν)
  filter_upwards [hsurv, hholes] with ω hs hh
  refine ⟨fun p => ?_, fun x => ?_⟩
  · obtain ⟨t₀, ht₀⟩ := hs p.1
    refine ⟨t₀, fun t ht => ?_⟩
    have := inactive_of_survivorsFrom_eq_zero (D := toDriver ω) ht₀ p.2 t ht
    simpa using this
  · obtain ⟨t₀, ht₀⟩ := hh x
    refine ⟨t₀, fun t ht => ?_⟩
    have hmono := LatticeProb.holeCount_antitone (toDriver ω) x ht
    have : Parking.H ω t x ≤ Parking.H ω t₀ x := hmono
    omega

end Parking
