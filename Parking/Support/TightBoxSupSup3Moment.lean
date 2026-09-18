/-
The `p`-th moment of `Parking.yfieldSup3` (`TightBoxSupAssemble.lean`), bounded by a constant
(depending only on `p`) TIMES `(R + 1) ^ 2` — completing route A's target `E[sup_{box(A)}
|Yfield|^p] ≤ poly(A)` (task item (c) up to the final Lyapunov step).  Combines the three
already-proven moment bounds (`Parking.exists_level0Max_moment`, `Parking.
exists_levelIncFixed_sum_moment`, `Parking.exists_dtail_moment_uniform`) via TWO nested
applications of `Parking.rpow_add_le_two`, the unweighted two-term power-mean bound (transported
from `NNReal.rpow_add_le_mul_rpow_add_rpow`, already in Mathlib).
-/
import Parking.Support.TightBoxSupAssemble
import Parking.Support.TightBoxSupTailAntitone
import Parking.Generic.PolyGrowth

open MeasureTheory LatticeProb Filter Topology Parking.Generic.PolyGrowth
open scoped NNReal

noncomputable section

namespace Parking

/-- **The unweighted two-term power-mean bound**, transported from `NNReal.
rpow_add_le_mul_rpow_add_rpow` (already proved in Mathlib). -/
theorem rpow_add_le_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℝ) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow a b hp

/-- **The `p`-th moment of `yfieldSup3` is bounded by a constant times `(R+1)^2`, uniform in the
scale `n`.** -/
theorem exists_yfieldSup3_moment (ν : Measure ℤ) (hν : CriticalLaw ν) (p : ℝ) (hp : 12 < p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (hA : 0 ≤ A), ∃ D : ℝ, 0 ≤ D ∧ D ≤ K * (1 + A) ^ (p / 2) ∧
      ∀ (R n : ℕ), 1 ≤ n →
      Integrable (fun η : Site 2 → ℝ => (yfieldSup3 A hA R n η) ^ p) (iidLaw 2 (realLaw ν)) ∧
      (∫ η : Site 2 → ℝ, (yfieldSup3 A hA R n η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
        D * (((R : ℝ) + 1) ^ 2) := by
  haveI : IsProbabilityMeasure ν := hν.prob
  haveI : IsProbabilityMeasure (realLaw ν) := realLaw_isProbability ν
  haveI : IsProbabilityMeasure (iidLaw 2 (realLaw ν)) := by unfold iidLaw; infer_instance
  have hp1 : (1:ℝ) ≤ p := by linarith
  have hp2 : (0:ℝ) ≤ p / 2 := by linarith
  set K0 : ℝ := (2:ℝ) ^ (p - 1) with hK0def
  have hK0nn : 0 ≤ K0 := by rw [hK0def]; positivity
  obtain ⟨M0, hM0, hb0⟩ := exists_level0Max_moment ν hν p (by linarith)
  obtain ⟨K1, hK1nn, hK1all⟩ := exists_levelIncFixed_sum_moment ν hν p hp
  obtain ⟨K2, hK2nn, hK2all⟩ := exists_dtail_moment_uniform ν hν p hp
  refine ⟨K0 * K0 * (2:ℝ) ^ p * (K1 + K2) + K0 * 4 * M0, by positivity, fun A hA => ?_⟩
  obtain ⟨C1, hC1, hC1bd, hb1⟩ := hK1all A hA
  obtain ⟨C2, hC2, hC2bd, hb2⟩ := hK2all A hA
  set D : ℝ := K0 * 4 * M0 + K0 * K0 * (2:ℝ) ^ p * C1 + K0 * K0 * (2:ℝ) ^ p * C2 with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  refine ⟨D, hDnn, ?_, fun R n hn => ?_⟩
  · -- The explicit polynomial-in-`A` bound on the witness `D`.
    have h1 : K0 * K0 * (2:ℝ) ^ p * C1 ≤ K0 * K0 * (2:ℝ) ^ p * (K1 * (1 + A) ^ (p / 2)) :=
      mul_le_mul_of_nonneg_left hC1bd (by positivity)
    have h2 : K0 * K0 * (2:ℝ) ^ p * C2 ≤ K0 * K0 * (2:ℝ) ^ p * (K2 * (1 + A) ^ (p / 2)) :=
      mul_le_mul_of_nonneg_left hC2bd (by positivity)
    have hx2 : D ≤ (K0 * K0 * (2:ℝ) ^ p * K1 + K0 * K0 * (2:ℝ) ^ p * K2) * (1 + A) ^ (p / 2) +
        K0 * 4 * M0 := by
      calc D = K0 * 4 * M0 + K0 * K0 * (2:ℝ) ^ p * C1 + K0 * K0 * (2:ℝ) ^ p * C2 := hDdef
        _ ≤ K0 * 4 * M0 + K0 * K0 * (2:ℝ) ^ p * (K1 * (1 + A) ^ (p / 2)) +
              K0 * K0 * (2:ℝ) ^ p * (K2 * (1 + A) ^ (p / 2)) := by linarith [h1, h2]
        _ = (K0 * K0 * (2:ℝ) ^ p * K1 + K0 * K0 * (2:ℝ) ^ p * K2) * (1 + A) ^ (p / 2) +
              K0 * 4 * M0 := by ring
    have hfinal := le_add_const_mul_one_add_rpow (by positivity : (0:ℝ) ≤ K0 * 4 * M0) hA hp2 hx2
    have heq : K0 * K0 * (2:ℝ) ^ p * K1 + K0 * K0 * (2:ℝ) ^ p * K2 + K0 * 4 * M0 =
        K0 * K0 * (2:ℝ) ^ p * (K1 + K2) + K0 * 4 * M0 := by ring
    rwa [heq] at hfinal
  set G1 : (Site 2 → ℝ) → ℝ := fun η => ∑ s ∈ Finset.range R, levelIncFixed A hA R n (s+1) η
    with hG1def
  set G2 : (Site 2 → ℝ) → ℝ := fun η => LatticeProb.dtail (fun m => levelInc A hA n m η) R
    with hG2def
  set G0 : (Site 2 → ℝ) → ℝ := fun η => level0Max A hA R n η with hG0def
  have hG0nn : ∀ η, 0 ≤ G0 η := fun η => level0Max_nonneg A hA R n η
  have hG1nn : ∀ η, 0 ≤ G1 η :=
    fun η => Finset.sum_nonneg fun k _ => levelIncFixed_nonneg A hA R n (k+1) η
  have hG2nn : ∀ η, 0 ≤ G2 η :=
    fun η => LatticeProb.dtail_nonneg (fun m => levelInc_nonneg A hA n m η) R
  have hyeq : ∀ η, yfieldSup3 A hA R n η = G0 η + (2 * G1 η + 2 * G2 η) := by
    intro η; rw [yfieldSup3]; ring
  have hG0int := hb0 A hA R n hn
  have hG1int := hb1 R n hn
  have hG2int := hb2 R n hn
  have hG1powint : Integrable (fun η => (2 * G1 η) ^ p) (iidLaw 2 (realLaw ν)) := by
    have heq : (fun η => (2 * G1 η) ^ p) = (fun η => (2:ℝ) ^ p * (G1 η) ^ p) := by
      funext η; rw [Real.mul_rpow (by norm_num) (hG1nn η)]
    rw [heq]; exact hG1int.1.const_mul _
  have hG2powint : Integrable (fun η => (2 * G2 η) ^ p) (iidLaw 2 (realLaw ν)) := by
    have heq : (fun η => (2 * G2 η) ^ p) = (fun η => (2:ℝ) ^ p * (G2 η) ^ p) := by
      funext η; rw [Real.mul_rpow (by norm_num) (hG2nn η)]
    rw [heq]; exact hG2int.1.const_mul _
  -- Pointwise bound, via two nested applications of `rpow_add_le_two`.
  have hpointwise : ∀ η, (yfieldSup3 A hA R n η) ^ p ≤
      K0 * (G0 η ^ p + (K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p))) := by
    intro η
    rw [hyeq η]
    have hstep1 := rpow_add_le_two (G0 η) (2 * G1 η + 2 * G2 η) (hG0nn η)
      (by linarith [hG1nn η, hG2nn η]) p hp1
    have hstep2 := rpow_add_le_two (2 * G1 η) (2 * G2 η) (by linarith [hG1nn η])
      (by linarith [hG2nn η]) p hp1
    have hmono : K0 * (2 * G1 η + 2 * G2 η) ^ p ≤
        K0 * (K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p)) :=
      mul_le_mul_of_nonneg_left hstep2 hK0nn
    calc (G0 η + (2 * G1 η + 2 * G2 η)) ^ p
        ≤ K0 * (G0 η ^ p + (2 * G1 η + 2 * G2 η) ^ p) := by rw [hK0def]; exact hstep1
      _ ≤ K0 * (G0 η ^ p + (K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p))) := by
          nlinarith [hmono]
  have hrhs_int : Integrable (fun η =>
      K0 * (G0 η ^ p + (K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p))))
      (iidLaw 2 (realLaw ν)) :=
    (hG0int.1.add ((hG1powint.add hG2powint).const_mul _)).const_mul _
  have hmeas_lhs : AEStronglyMeasurable (fun η => (yfieldSup3 A hA R n η) ^ p)
      (iidLaw 2 (realLaw ν)) := by
    have heq : (fun η => (yfieldSup3 A hA R n η) ^ p) =
        (fun η => |yfieldSup3 A hA R n η| ^ p) := by
      funext η; rw [abs_of_nonneg (yfieldSup3_nonneg A hA R n η)]
    rw [heq]
    have hmeasY : AEStronglyMeasurable (fun η => yfieldSup3 A hA R n η)
        (iidLaw 2 (realLaw ν)) := by
      have heqY : (fun η => yfieldSup3 A hA R n η) = fun η => G0 η + 2 * G1 η + 2 * G2 η := by
        funext η; rw [yfieldSup3]
      rw [heqY]
      have hG0meas : Measurable G0 := measurable_level0Max A hA R n
      have hG1meas : Measurable G1 :=
        Finset.measurable_fun_sum _ fun k _ => measurable_levelIncFixed A hA R n (k+1)
      have hG2aesm : AEStronglyMeasurable G2 (iidLaw 2 (realLaw ν)) := by
        set T : ℕ → (Site 2 → ℝ) → ℝ :=
          fun N η => ∑ k ∈ Finset.range (N+1), levelInc A hA n (R + 1 + k) η with hTdef
        have hTmeas : ∀ N, Measurable (T N) :=
          fun N => Finset.measurable_fun_sum _ fun k _ => measurable_levelInc A hA n (R+1+k)
        have hae_tendsto : ∀ᵐ η ∂(iidLaw 2 (realLaw ν)),
            Tendsto (fun N => T N η) atTop (𝓝 (G2 η)) := by
          filter_upwards [ae_summable_levelInc ν hν hA n hn R] with η hsum
          have hshift : Summable (fun k : ℕ => levelInc A hA n (R + 1 + k) η) := by
            have hs := (summable_nat_add_iff (R + 1)).mpr hsum
            refine hs.congr fun k => ?_
            congr 1
            omega
          have htendsto := hshift.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
          have hG2eq : G2 η = ∑' k : ℕ, levelInc A hA n (R + 1 + k) η := by
            show LatticeProb.dtail (fun m => levelInc A hA n m η) R = _
            simp only [LatticeProb.dtail]
            apply tsum_congr
            intro i
            congr 1
            omega
          rwa [hG2eq]
        exact aestronglyMeasurable_of_tendsto_ae atTop
          (fun N => (hTmeas N).aestronglyMeasurable) hae_tendsto
      exact ((hG0meas.aestronglyMeasurable.add
        ((hG1meas.const_mul 2).aestronglyMeasurable)).add (hG2aesm.const_mul 2))
    have hcont : Continuous (fun t : ℝ => |t| ^ p) :=
      continuous_abs.rpow_const (fun t => Or.inr (by linarith))
    exact hcont.comp_aestronglyMeasurable hmeasY
  have hlhs_int : Integrable (fun η => (yfieldSup3 A hA R n η) ^ p) (iidLaw 2 (realLaw ν)) := by
    refine hrhs_int.mono' hmeas_lhs (Filter.Eventually.of_forall fun η => ?_)
    have hnn : (0:ℝ) ≤ (yfieldSup3 A hA R n η) ^ p :=
      Real.rpow_nonneg (yfieldSup3_nonneg A hA R n η) p
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hpointwise η
  refine ⟨hlhs_int, ?_⟩
  have hRR1 : (1:ℝ) ≤ (((R:ℝ)+1)^2) := by nlinarith [Nat.cast_nonneg (α := ℝ) R]
  have hG0_bound' : (∫ η, (G0 η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤ 4 * M0 * (((R:ℝ)+1)^2) := by
    have hle := hG0int.2
    have h1 : (2*(R:ℝ)+1) ≤ 2*((R:ℝ)+1) := by linarith
    have h2 : (2*(R:ℝ)+1)^2 ≤ (2*((R:ℝ)+1))^2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (2*((R:ℝ)+1))^2 = 4*(((R:ℝ)+1)^2) := by ring
    nlinarith [hle, h2, h3, hM0]
  have hG1pow_bound : (∫ η, (2 * G1 η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
      (2:ℝ) ^ p * C1 * (((R:ℝ)+1)^2) := by
    have heq : (fun η => (2 * G1 η) ^ p) = (fun η => (2:ℝ) ^ p * (G1 η) ^ p) := by
      funext η; rw [Real.mul_rpow (by norm_num) (hG1nn η)]
    rw [heq, integral_const_mul]
    calc (2:ℝ) ^ p * (∫ η, (G1 η) ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ (2:ℝ) ^ p * (C1 * (((R:ℝ)+1)^2)) :=
          mul_le_mul_of_nonneg_left hG1int.2 (by positivity)
      _ = (2:ℝ) ^ p * C1 * (((R:ℝ)+1)^2) := by ring
  have hG2pow_bound : (∫ η, (2 * G2 η) ^ p ∂(iidLaw 2 (realLaw ν))) ≤
      (2:ℝ) ^ p * C2 * (((R:ℝ)+1)^2) := by
    have heq : (fun η => (2 * G2 η) ^ p) = (fun η => (2:ℝ) ^ p * (G2 η) ^ p) := by
      funext η; rw [Real.mul_rpow (by norm_num) (hG2nn η)]
    rw [heq, integral_const_mul]
    calc (2:ℝ) ^ p * (∫ η, (G2 η) ^ p ∂(iidLaw 2 (realLaw ν)))
        ≤ (2:ℝ) ^ p * C2 :=
          mul_le_mul_of_nonneg_left hG2int.2 (by positivity)
      _ ≤ (2:ℝ) ^ p * C2 * (((R:ℝ)+1)^2) := by
          have hnn2 : (0:ℝ) ≤ (2:ℝ) ^ p * C2 := by positivity
          calc (2:ℝ) ^ p * C2 = (2:ℝ) ^ p * C2 * 1 := (mul_one _).symm
            _ ≤ (2:ℝ) ^ p * C2 * (((R:ℝ)+1)^2) := mul_le_mul_of_nonneg_left hRR1 hnn2
  calc (∫ η, (yfieldSup3 A hA R n η) ^ p ∂(iidLaw 2 (realLaw ν)))
      ≤ ∫ η, K0 * (G0 η ^ p + (K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p)))
          ∂(iidLaw 2 (realLaw ν)) :=
        integral_mono_ae hlhs_int hrhs_int (Filter.Eventually.of_forall hpointwise)
    _ = K0 * ((∫ η, (G0 η) ^ p ∂(iidLaw 2 (realLaw ν))) +
          K0 * ((∫ η, (2 * G1 η) ^ p ∂(iidLaw 2 (realLaw ν))) +
            (∫ η, (2 * G2 η) ^ p ∂(iidLaw 2 (realLaw ν))))) := by
        have hstepA : (∫ η, (2 * G1 η) ^ p + (2 * G2 η) ^ p ∂(iidLaw 2 (realLaw ν))) =
            (∫ η, (2 * G1 η) ^ p ∂(iidLaw 2 (realLaw ν))) +
              (∫ η, (2 * G2 η) ^ p ∂(iidLaw 2 (realLaw ν))) :=
          integral_add hG1powint hG2powint
        have hint2 : Integrable (fun η => K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p))
            (iidLaw 2 (realLaw ν)) := (hG1powint.add hG2powint).const_mul _
        have hstepC := integral_add hG0int.1 hint2
        have hstepD := integral_const_mul (μ := iidLaw 2 (realLaw ν)) K0
          (fun η => (2 * G1 η) ^ p + (2 * G2 η) ^ p)
        have hstepB : (∫ η, G0 η ^ p + K0 * ((2 * G1 η) ^ p + (2 * G2 η) ^ p)
            ∂(iidLaw 2 (realLaw ν))) =
            (∫ η, G0 η ^ p ∂(iidLaw 2 (realLaw ν))) +
              K0 * (∫ η, (2 * G1 η) ^ p + (2 * G2 η) ^ p ∂(iidLaw 2 (realLaw ν))) := by
          rw [hstepC, hstepD]
        rw [integral_const_mul, hstepB, hstepA]
    _ ≤ K0 * (4 * M0 * (((R:ℝ)+1)^2) +
          K0 * (((2:ℝ) ^ p * C1 * (((R:ℝ)+1)^2)) + ((2:ℝ) ^ p * C2 * (((R:ℝ)+1)^2)))) := by
        gcongr
    _ = D * (((R:ℝ)+1)^2) := by
        rw [hDdef]; ring

end Parking

end
