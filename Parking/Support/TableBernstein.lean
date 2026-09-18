import Parking.Support.WeightedOdometerBounds
import Parking.Support.BoundedMoment
import Parking.Support.TableDifferenceSum
import Parking.External.Bernstein

noncomputable section
namespace Parking
open MeasureTheory LatticeProb
variable {d : ℕ}

/-- Bernstein's inequality applied to the constructed chronological odometer martingale. -/
theorem exists_table_noise_moment_bound (hBernstein : External.Bernstein) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 3 ≤ d → ∀ (η : Site d → ℤ),
      (∀ y, (η y).toNat ≤ 1) → ∀ (ρ : Label d × ℕ → ℝ) (T : ℕ) (x : Site d) (r : ℝ), 2 ≤ r →
      rNorm (flatRoundNoiseLaw d) r (fun ω => ((matchedState η ρ (curryRoundNoise ω) T).departures x : ℝ) - matchedMeanU η ρ T x) ≤
        C * (Real.sqrt r * (∫ ω, greenWeightedOdometer η ρ (curryRoundNoise ω) T x T ^ (r / 2)
          ∂(flatRoundNoiseLaw d)) ^ (1 / r) + r * escapeConst d) := by
  obtain ⟨C, hC, hBern⟩ := hBernstein
  refine ⟨C, hC, fun d hd η hη ρ T x r hr => ?_⟩
  have hd1 : 1 ≤ d := by omega
  haveI := flatRoundNoiseLaw_isProbability hd1
  let N := (2 * T + 1) ^ d
  let K := (roundEntrySet x T N).card
  let e := roundEnumeration x T N
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : 0 < K := roundEntrySet_card_pos x T N hN
  let base : FlatRoundNoise d := fun _ => (⟨0, hd1⟩, false)
  let F := tableFiltration base e
  let ξ := tableDiff η ρ T x e hK
  let μ := flatRoundNoiseLaw d
  have hi (n : ℕ) : Integrable (ξ n) μ := (integrable_tableDiff hd η hη ρ T x e hK n).1
  have hmean (n : ℕ) (hn : 1 ≤ n) (_hnK : n ≤ T * K) : μ[ξ n | F (n - 1)] =ᵐ[μ] 0 := by
    have h := condExp_tableDiff_zero hd base η hη ρ T x e hK (n - 1)
    rw [Nat.sub_add_cancel hn] at h
    exact h
  have ha : 0 < escapeConst d := zero_lt_one.trans_le (one_le_escapeConst hd)
  have hb := (hBern (FlatRoundNoise d) inferInstance μ inferInstance (T * K) F ξ r (escapeConst d)
    (tableFiltration_mono base e) (tableFiltration_le base e)
    (measurable_tableDiff_adapted hd1 base η ρ T x e hK) hi hmean hr ha).1
      (fun n _hn _hnK ω => abs_tableDiff_le hd η hη ρ T x e hK n ω)
  have hsum (ω : FlatRoundNoise d) : (∑ n ∈ Finset.Icc 1 (T * K), ξ n ω) =
      ((matchedState η ρ (curryRoundNoise ω) T).departures x : ℝ) - matchedMeanU η ρ T x :=
    sum_tableDiff hd1 η hη ρ T x e hK
      (fun y hy j hj => roundEnumeration_covers x T N y j hy hj) ω
  simp only [hsum] at hb
  let V : FlatRoundNoise d → ℝ := fun ω => ∑ n ∈ Finset.Icc 1 (T * K), (μ[fun ζ => ξ n ζ ^ 2 | F (n - 1)]) ω
  let Q : FlatRoundNoise d → ℝ := fun ω => greenWeightedOdometer η ρ (curryRoundNoise ω) T x T
  have hV0 : ∀ᵐ ω ∂μ, 0 ≤ V ω := by
    have hn : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 ≤ (μ[fun ζ => ξ n ζ ^ 2 | F (n - 1)]) ω :=
      ae_all_iff.mpr fun n => condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)
    filter_upwards [hn] with ω hω
    exact Finset.sum_nonneg fun n _ => hω n
  have hVQ : V ≤ᵐ[μ] Q := tableDiff_qv_le hd base η hη ρ T x T N le_rfl hK
  let B : ℝ := (∑ v ∈ boxFinset x T, walkOp (fun y => fullGreen d (y - x) ^ 2) v) * ((T * (2 * T + 1) ^ d : ℕ) : ℝ)
  have hQB (ω : FlatRoundNoise d) : |Q ω| ≤ B := by
    rw [abs_of_nonneg (greenWeightedOdometer_nonneg _ _ _ _ _ _)]
    exact greenWeightedOdometer_le_box η hη ρ _ T x T
  have hQi : Integrable (fun ω => Q ω ^ (r / 2)) μ := by
    have hiQ := integrable_abs_rpow_bounded μ Q (measurable_greenWeightedOdometer hd1 η ρ T x T)
      B hQB (by linarith : 0 ≤ r / 2)
    have hQ0 (ω : FlatRoundNoise d) : 0 ≤ Q ω := greenWeightedOdometer_nonneg η ρ _ T x T
    have he : (fun ω => |Q ω| ^ (r / 2)) = (fun ω => Q ω ^ (r / 2)) :=
      funext fun ω => by rw [abs_of_nonneg (hQ0 ω)]
    exact he ▸ hiQ
  have hVint : 0 ≤ ∫ ω, V ω ^ (r / 2) ∂μ :=
    integral_nonneg_of_ae (hV0.mono fun _ h => Real.rpow_nonneg h _)
  have hIq : (∫ ω, V ω ^ (r / 2) ∂μ) ≤ ∫ ω, Q ω ^ (r / 2) ∂μ := by
    apply integral_mono_of_nonneg (hV0.mono fun _ h => Real.rpow_nonneg h _) hQi
    filter_upwards [hV0, hVQ] with ω hn hle
    exact Real.rpow_le_rpow hn hle (by linarith)
  have hroot := Real.rpow_le_rpow hVint hIq (by positivity : (0 : ℝ) ≤ 1 / r)
  exact hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg r)) (le_refl (r * escapeConst d))) hC.le)
end Parking
