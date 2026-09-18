/-
The mean odometer at the limit horizon as a sum of survivor counts
(`parking.tex:2578-2583`).

"Thus `E U_∞^δ(0) = ∑_{t≥0} S_t^δ`."

The limit mean is the lower integral of the pointwise supremum of the odometers at
the finite horizons, and the odometer is the sum of the round activities, so it
increases with the horizon and monotone convergence turns the limit mean into the
supremum of the finite means.  `eq:transport` then reads each finite mean as a sum
of survivor counts, and a bound on the tail of that sum which is uniform in the
upper limit bounds the limit mean.
-/
import Parking.Support.CriticalChain
import Parking.Support.MassTransport
import Parking.Support.Transport
import Parking.Support.Measurability

open MeasureTheory LatticeProb
open scoped ENNReal

noncomputable section
namespace Parking
variable {d : ℕ}

/-- The particle odometer increases with the horizon. -/
theorem U_mono_time (ω : Data d) (x : Site d) {n m : ℕ} (h : n ≤ m) :
    Parking.U ω n x ≤ Parking.U ω m x := by
  rw [Parking.U_eq_sum_A ω n x, Parking.U_eq_sum_A ω m x]
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- **Monotone convergence for the limit odometer.**  The limit mean is the supremum
of the means at the finite horizons. -/
theorem meanUlimit_eq_iSup (hd : 1 ≤ d) (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun k : ℤ => |(k : ℝ)|) ν) :
    Parking.meanUlimit (Parking.law d ν)
      = ⨆ n : ℕ, ENNReal.ofReal (Parking.meanU (Parking.law d ν) n) := by
  have hmeas : ∀ n : ℕ, Measurable (fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ≥0∞)) := by
    intro n
    exact (measurable_from_countable' (fun m : ℕ => (m : ℝ≥0∞))).comp (measurable_U n 0)
  have hmono : Monotone (fun n : ℕ => fun ω : Data d => ((Parking.U ω n 0 : ℕ) : ℝ≥0∞)) := by
    intro n m hnm ω
    exact Nat.cast_le.mpr (U_mono_time ω 0 hnm)
  have hpt : ∀ ω : Data d, ((Parking.Ulimit ω 0 : ℕ∞) : ℝ≥0∞)
      = ⨆ n : ℕ, ((Parking.U ω n 0 : ℕ) : ℝ≥0∞) := by
    intro ω
    rw [Parking.Ulimit, ENat.toENNReal_iSup]
    rfl
  have hstep : ∀ n : ℕ, ∫⁻ ω, ((Parking.U ω n 0 : ℕ) : ℝ≥0∞) ∂(Parking.law d ν)
      = ENNReal.ofReal (Parking.meanU (Parking.law d ν) n) := by
    intro n
    rw [Parking.meanU, ofReal_integral_eq_lintegral_ofReal
      (Parking.integrable_U_law hd ν hint n 0)
      (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg _)]
    exact lintegral_congr fun ω => (ENNReal.ofReal_natCast _).symm
  calc Parking.meanUlimit (Parking.law d ν)
      = ∫⁻ ω, ⨆ n : ℕ, ((Parking.U ω n 0 : ℕ) : ℝ≥0∞) ∂(Parking.law d ν) :=
        lintegral_congr hpt
    _ = ⨆ n : ℕ, ∫⁻ ω, ((Parking.U ω n 0 : ℕ) : ℝ≥0∞) ∂(Parking.law d ν) :=
        lintegral_iSup hmeas hmono
    _ = ⨆ n : ℕ, ENNReal.ofReal (Parking.meanU (Parking.law d ν) n) := iSup_congr hstep

/-- A tail sum bounded by the tail of a summable series with a bounded total. -/
theorem sum_Ico_le_of_tsum {f g : ℕ → ℝ} {T C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hg : ∀ t : ℕ, 0 ≤ g t)
    (hfg : ∀ t : ℕ, f t ≤ C * g t) (hNT : T < (N : ℝ))
    (hsum : Summable (fun t : ℕ => if T < (t : ℝ) then g t else 0))
    (htot : ∑' t : ℕ, (if T < (t : ℝ) then g t else 0) ≤ 1) (n : ℕ) :
    ∑ s ∈ Finset.Ico N n, f s ≤ C := by
  have hstep : ∀ s ∈ Finset.Ico N n, f s ≤ C * (if T < (s : ℝ) then g s else 0) := by
    intro s hs
    have hNs : N ≤ s := (Finset.mem_Ico.mp hs).1
    have hTs : T < (s : ℝ) := lt_of_lt_of_le hNT (by exact_mod_cast hNs)
    rw [if_pos hTs]
    exact hfg s
  have hnonneg : ∀ i : ℕ, i ∉ Finset.Ico N n → 0 ≤ (if T < (i : ℝ) then g i else 0) := by
    intro i _
    by_cases hi : T < (i : ℝ)
    · rw [if_pos hi]; exact hg i
    · rw [if_neg hi]
  calc ∑ s ∈ Finset.Ico N n, f s
      ≤ ∑ s ∈ Finset.Ico N n, C * (if T < (s : ℝ) then g s else 0) := Finset.sum_le_sum hstep
    _ = C * ∑ s ∈ Finset.Ico N n, (if T < (s : ℝ) then g s else 0) := by rw [Finset.mul_sum]
    _ ≤ C * ∑' t : ℕ, (if T < (t : ℝ) then g t else 0) :=
        mul_le_mul_of_nonneg_left (Summable.sum_le_tsum _ hnonneg hsum) hC
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left htot hC
    _ = C := mul_one C

end Parking
end
