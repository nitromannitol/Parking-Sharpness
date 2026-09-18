/-
Mass transport for surviving discrepancy labels. Finite speed expresses sent
and received mass as finite sums. Translation covariance and invariance of
the full coupling law identify their nonnegative expectations.
-/
import Parking.Support.DiscrepancyShift
import Parking.Support.CoupledInvariance
import Parking.Support.DiscrepancyMeas
import Parking.Support.MassTransport

noncomputable section

open MeasureTheory LatticeProb
open scoped ENNReal

variable {d : ℕ}

/-- Labels surviving from their creation site. -/
def Parking.discrepancySurvivors (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (a : Site d) : ℕ :=
  ((Finset.range (Parking.discrepancyConf c a).toNat).filter fun i =>
    (Parking.discrepancyState c ρ σ t).active (a, i)).card

/-- Surviving labels send one unit of mass from their creation site to their position. -/
def Parking.discrepancySentTo (c : Site d → ℤ × ℤ) (ρ : Label d × ℕ → ℝ)
    (σ : Parking.RoundNoise d) (t : ℕ) (a b : Site d) : ℕ :=
  ((Finset.range (Parking.discrepancyConf c a).toNat).filter fun i =>
    (Parking.discrepancyState c ρ σ t).active (a, i) ∧
      (Parking.discrepancyState c ρ σ t).pos (a, i) = b).card

theorem Parking.discrepancyAt_eq_sum_sentTo (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (b : Site d) :
    (Parking.discrepancyAt c (Parking.discrepancyState c ρ σ t) t b).card =
      ∑ a ∈ boxFinset b t, Parking.discrepancySentTo c ρ σ t a b := by
  classical
  exact Parking.card_filter_candidates_eq_sum (Parking.discrepancyConf c) b t _

theorem Parking.discrepancySurvivors_eq_sum_sentTo (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (a : Site d) :
    Parking.discrepancySurvivors c ρ σ t a =
      ∑ b ∈ boxFinset a t, Parking.discrepancySentTo c ρ σ t a b := by
  classical
  have hmem : ∀ i ∈ (Finset.range (Parking.discrepancyConf c a).toNat).filter
      (fun i => (Parking.discrepancyState c ρ σ t).active (a, i) = true),
      (Parking.discrepancyState c ρ σ t).pos (a, i) ∈ boxFinset a t := by
    intro i _
    exact mem_boxFinset_iff.mpr (Parking.abs_discrepancyPos_sub_start_le c ρ σ t (a, i))
  rw [Parking.discrepancySurvivors, Finset.card_eq_sum_card_fiberwise hmem]
  apply Finset.sum_congr rfl
  intro b _
  rw [Parking.discrepancySentTo, Finset.filter_filter]

theorem Parking.discrepancySentTo_shift (v : Site d) (c : Site d → ℤ × ℤ)
    (ρ : Label d × ℕ → ℝ) (σ : Parking.RoundNoise d) (t : ℕ) (a b : Site d) :
    Parking.discrepancySentTo (fun y => c (y + v)) (Parking.shiftRank v ρ)
      (Parking.shiftRoundNoise v σ) t a b = Parking.discrepancySentTo c ρ σ t (a + v) (b + v) := by
  classical
  have hS := Parking.discrepancyState_shift v c ρ σ t
  unfold Parking.discrepancySentTo
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Parking.discrepancyConf,
    hS.active, hS.pos, Parking.shiftLabel, sub_eq_iff_eq_add]

/-- Joint measurability of the label mass sent between two sites. -/
theorem Parking.measurable_discrepancySentTo (hd : 1 ≤ d) (t : ℕ) (a b : Site d) :
    Measurable fun ω : Parking.CoupledData d => Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t a b := by
  classical
  have hS := Parking.measurableState_discrepancyState (Ω := Parking.CoupledData d) ⟨0, hd⟩
    (fun ω => ω.1.1) (fun ω => ω.1.2) Prod.snd
    (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst) measurable_snd t
  have hN : Measurable fun ω : Parking.CoupledData d => (Parking.discrepancyConf ω.1.1 a).toNat :=
    (measurable_of_countable (fun z : ℤ => z.toNat)).comp
      ((measurable_pi_apply a).comp (Parking.measurable_discrepancyConf
        (fun ω : Parking.CoupledData d => ω.1.1) (measurable_fst.comp measurable_fst)))
  apply (measurable_of_countable (Finset.card (α := ℕ))).comp
  apply measurable_finset_iff.mpr
  intro i
  simp only [Finset.mem_filter, Finset.mem_range]
  have hact := hS.1 (a, i)
  have hpos := hS.2.1 (a, i)
  fun_prop

/-- The expected received and sent label masses agree. -/
theorem Parking.lintegral_discrepancyAt_eq_survivors (hd : 1 ≤ d) (ν : Measure ℤ)
    [IsProbabilityMeasure ν] {p : ℝ≥0∞} (hp : p ≤ 1) (t : ℕ) :
    ∫⁻ ω : Parking.CoupledData d,
        ((Parking.discrepancyAt ω.1.1 (Parking.discrepancyState ω.1.1 ω.1.2 ω.2 t) t 0).card : ℝ≥0∞)
        ∂(Parking.coupledLaw d ν p) =
      ∫⁻ ω : Parking.CoupledData d,
        (Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) := by
  classical
  have hm : ∀ a b : Site d, Measurable fun ω : Parking.CoupledData d =>
      (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t a b : ℝ≥0∞) := fun a b =>
    (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (Parking.measurable_discrepancySentTo hd t a b)
  have hA : ∫⁻ ω : Parking.CoupledData d,
      ((Parking.discrepancyAt ω.1.1 (Parking.discrepancyState ω.1.1 ω.1.2 ω.2 t) t 0).card : ℝ≥0∞)
      ∂(Parking.coupledLaw d ν p) =
      ∑ a ∈ boxFinset (0 : Site d) t, ∫⁻ ω : Parking.CoupledData d,
        (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t a 0 : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) := by
    rw [← lintegral_finsetSum _ fun a _ => hm a 0]
    apply lintegral_congr
    intro ω
    exact_mod_cast Parking.discrepancyAt_eq_sum_sentTo ω.1.1 ω.1.2 ω.2 t 0
  have hS : ∫⁻ ω : Parking.CoupledData d,
      (Parking.discrepancySurvivors ω.1.1 ω.1.2 ω.2 t 0 : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) =
      ∑ b ∈ boxFinset (0 : Site d) t, ∫⁻ ω : Parking.CoupledData d,
        (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t 0 b : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) := by
    rw [← lintegral_finsetSum _ fun b _ => hm 0 b]
    apply lintegral_congr
    intro ω
    exact_mod_cast Parking.discrepancySurvivors_eq_sum_sentTo ω.1.1 ω.1.2 ω.2 t 0
  have htrans : ∀ a : Site d, ∫⁻ ω : Parking.CoupledData d,
      (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t a 0 : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) =
      ∫⁻ ω : Parking.CoupledData d,
      (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t 0 (-a) : ℝ≥0∞) ∂(Parking.coupledLaw d ν p) := by
    intro a
    have h := lintegral_map (μ := Parking.coupledLaw d ν p) (hm a 0)
      (Parking.measurable_shiftCoupledData (-a))
    rw [Parking.coupledLaw_map_shift hd ν hp] at h
    simpa only [Parking.shiftCoupledData, Parking.discrepancySentTo_shift,
      add_neg_cancel, zero_add] using h
  rw [hA, hS, Finset.sum_congr rfl fun a _ => htrans a]
  exact Parking.sum_neg_box t (fun b : Site d => ∫⁻ ω : Parking.CoupledData d,
    (Parking.discrepancySentTo ω.1.1 ω.1.2 ω.2 t 0 b : ℝ≥0∞) ∂(Parking.coupledLaw d ν p))

end
